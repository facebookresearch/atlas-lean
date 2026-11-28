# Unit-step predictive coding computes exact gradients in depth-many iterations

**Setting.** Use the feedforward network $\hat v_0 = x$, $\hat v_\ell = f_\ell(\hat v_{\ell-1}; \theta_\ell)$ ($\ell = 1, \dots, L$), loss $\mathcal L(\hat y, y)$ with $\hat y = \hat v_L$, and predictive coding under the fixed prediction assumption: beliefs start at $v^0_\ell = \hat v_\ell$, the output error $\epsilon_L = \delta_L = \partial \mathcal L(\hat v_L, y)/\partial \hat v_L$ is fixed, and iteration $i = 1, \dots, n$ sweeps $\ell = L-1, \dots, 1$ computing

$$\epsilon^i_\ell = \hat v_\ell - v^{i-1}_\ell, \qquad dv^i_\ell = \epsilon^i_\ell - \epsilon^i_{\ell+1} \frac{\partial f_{\ell+1}(\hat v_\ell; \theta_{\ell+1})}{\partial \hat v_\ell}, \qquad v^i_\ell = v^{i-1}_\ell + \eta\, dv^i_\ell,$$

followed by $d\theta_\ell = -\epsilon_\ell\, \partial f_\ell(\hat v_{\ell-1}; \theta_\ell)/\partial \theta_\ell$. Because the sweep runs downward, $\epsilon_{\ell+1}$ in iteration $i$ is already the updated value $\epsilon^i_{\ell+1}$.

**Theorem.** If the step size is $\eta = 1$ and the number of iterations is $n \ge L$, then for all $\ell = 1, \dots, L$

$$\epsilon_\ell = \delta_\ell = \frac{\partial \mathcal L(\hat y, y)}{\partial \hat v_\ell}, \qquad d\theta_\ell = -\frac{\partial \mathcal L(\hat y, y)}{\partial \theta_\ell},$$

the exact backpropagation gradients, for arbitrary differentiable layer maps $f_\ell$ and an arbitrary differentiable loss. More precisely, for $\ell < L$, $\epsilon^i_\ell = 0$ for $i < L - \ell + 1$ and $\epsilon^i_\ell = \delta_\ell$ for every $i \ge L - \ell + 1$.

**Corollary (algorithmic equivalence).** With $\eta = 1$ each error $\epsilon_\ell$ changes exactly once, at iteration $L - \ell + 1$, so the double loop performs exactly the backward pass $\epsilon_\ell = \epsilon_{\ell+1}\, \partial f_{\ell+1}(\hat v_\ell; \theta_{\ell+1})/\partial \hat v_\ell$ for $\ell = L-1, \dots, 1$, with every other step computing zero. The fixed-point beliefs are recovered afterwards from $\epsilon_\ell = \hat v_\ell - v_\ell$. Any neural machinery able to run this form of predictive coding therefore runs backpropagation itself, which bears on claims that it is more biologically plausible.

## Expansion

With $\eta = 1$, $\epsilon^{i+1}_\ell = \hat v_\ell - v^i_\ell = \epsilon^i_\ell - dv^i_\ell = \epsilon^i_{\ell+1} J_{\ell+1}$, where $J_{\ell+1} = \partial f_{\ell+1}(\hat v_\ell; \theta_{\ell+1})/\partial \hat v_\ell$: the belief term cancels and each error copies the propagated error from the layer above. Since $v^0_\ell = \hat v_\ell$, $\epsilon^1_\ell = 0$ for $\ell < L$. Induct downward from $\ell = L$, where $\epsilon^i_L = \delta_L$ for all $i$: if $\epsilon^{i}_{\ell+1} = \delta_{\ell+1}$ from iteration $i = L-\ell$ on, then from iteration $L-\ell+1$ on, $\epsilon_\ell = \delta_{\ell+1} J_{\ell+1} = \partial \mathcal L/\partial \hat v_\ell$ by the chain rule, valid because $\hat v_{\ell+1} = f_{\ell+1}(\hat v_\ell; \theta_{\ell+1})$. The last layer reached is $\ell = 1$ at iteration $L$. The parameter statement follows from $d\theta_\ell = -\delta_\ell\, \partial \hat v_\ell/\partial \theta_\ell$. The result needs the forward-pass initialization; for $\eta < 1$ the errors only approach $\delta_\ell$ as $n$ grows. The source checks it on convolutional networks for MNIST and CIFAR-10, where errors vanish after $n = L$ iterations up to floating-point noise. The source prints the error in the pseudocode of its Algorithm 3 as $v_\ell - \hat v_\ell$; the convention of its Eq (12), used here, is the one under which the proof's cancellation holds.

## Depends on

- [Fixed points of predictive coding and the fixed prediction assumption](fixed-points-of-predictive-coding-under-the-fixed-prediction-assumption.md)

## Sources

- R. Rosenbaum, "On the relationship between predictive coding and backpropagation", PLoS ONE 17(3) (2022) e0266102, Theorem 1 and its proof, Eq (12), and the section showing equivalence with a direct implementation of backpropagation, <https://doi.org/10.1371/journal.pone.0266102>, PMCID PMC8970408.
