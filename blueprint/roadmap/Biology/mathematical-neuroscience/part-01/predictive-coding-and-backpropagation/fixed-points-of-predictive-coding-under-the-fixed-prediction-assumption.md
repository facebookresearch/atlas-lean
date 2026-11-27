# Fixed points of predictive coding and the fixed prediction assumption

**Network and model.** A feedforward network of depth $L$ is given by differentiable maps $f_\ell(\,\cdot\,;\theta_\ell)$, $\ell = 1, \dots, L$, and the forward pass

$$\hat v_0 = x, \qquad \hat v_\ell = f_\ell(\hat v_{\ell-1}; \theta_\ell), \qquad \hat y = \hat v_L,$$

with a differentiable loss $\mathcal L(\hat y, y)$ for a label $y$. Backpropagation computes $\delta_\ell = \partial \mathcal L / \partial \hat v_\ell$ by $\delta_\ell = \delta_{\ell+1}\, \partial f_{\ell+1}(\hat v_\ell; \theta_{\ell+1}) / \partial \hat v_\ell$ and the negative gradients $d\theta_\ell = -\delta_\ell\, \partial f_\ell(\hat v_{\ell-1}; \theta_\ell)/\partial \theta_\ell = -\partial \mathcal L / \partial \theta_\ell$ (errors are row vectors, Jacobians act on the right). Predictive coding interprets the network as a hierarchical Gaussian model $p(V_\ell = v_\ell \mid V_{\ell-1} = v_{\ell-1}) = \mathcal N(v_\ell; f_\ell(v_{\ell-1}; \theta_\ell), \Sigma_\ell)$, with $\Sigma_\ell = I$ unless stated otherwise.

**Strict predictive coding.** For beliefs $v_1, \dots, v_{L-1}$ (with $v_0 = x$) define the prediction errors $\epsilon_\ell = f_\ell(v_{\ell-1}; \theta_\ell) - v_\ell$ for $\ell < L$, the output error $\epsilon_L = f_L(v_{L-1}; \theta_L) - y$ for the squared loss $\mathcal L = \tfrac12 \lVert \hat y - y \rVert^2$, and the free energy $F = \tfrac12 \sum_{\ell=1}^{L} \lVert \epsilon_\ell \rVert^2$. Inference is gradient descent $v_\ell \leftarrow v_\ell + \eta\, dv_\ell$ with

$$dv_\ell = -\frac{\partial F}{\partial v_\ell} = \epsilon_\ell - \epsilon_{\ell+1} \frac{\partial f_{\ell+1}(v_\ell; \theta_{\ell+1})}{\partial v_\ell},$$

and learning uses $d\theta_\ell = -\partial F/\partial \theta_\ell = -\epsilon_\ell\, \partial f_\ell(v_{\ell-1}; \theta_\ell)/\partial \theta_\ell$.

**Claim 1 (strict fixed points are not gradients).** At any fixed point $v^*$ of the inference dynamics ($dv_\ell = 0$),

$$\epsilon^*_\ell = \epsilon^*_{\ell+1} \frac{\partial f_{\ell+1}(v^*_\ell; \theta_{\ell+1})}{\partial v^*_\ell}, \qquad \ell = 1, \dots, L-1,$$

so $\epsilon^*_{L-1} = \partial \mathcal L(\tilde v^*_L, y)/\partial v^*_{L-1}$ with $\tilde v^*_L = f_L(v^*_{L-1}; \theta_L)$, but for $\ell \le L-2$ the product of Jacobians evaluated at the beliefs $v^*$ does not collapse by the chain rule, because in general $v^*_\ell \ne f_\ell(v^*_{\ell-1}; \theta_\ell)$. The beliefs equal the forward pass exactly when all hidden errors vanish; the fixed-point equations then give $\delta_\ell = 0$ and $\partial \mathcal L/\partial \theta_\ell = 0$ for every hidden layer $\ell \le L-1$, while $d\theta_L = -\partial \mathcal L/\partial \theta_L$ need not vanish. (The source states the stronger claim that strict predictive coding agrees with backpropagation only at critical points of the loss; with $L = 2$, $f_1(x) = ax$, $f_2(v) = bv$, $a = x = y = 1$ and $b = 0$, the forward pass is a strict fixed point, both rules give $(da, db) = (0, 1)$, and $\partial\mathcal L/\partial b = -1$.)

**Fixed prediction assumption.** Replace predictions and Jacobians by their forward-pass values and initialize $v_\ell = \hat v_\ell$:

$$\epsilon_\ell = \hat v_\ell - v_\ell, \quad \epsilon_L = \frac{\partial \mathcal L(\hat v_L, y)}{\partial \hat v_L}, \quad dv_\ell = \epsilon_\ell - \epsilon_{\ell+1} \frac{\partial f_{\ell+1}(\hat v_\ell; \theta_{\ell+1})}{\partial \hat v_\ell}, \quad d\theta_\ell = -\epsilon_\ell \frac{\partial f_\ell(\hat v_{\ell-1}; \theta_\ell)}{\partial \theta_\ell},$$

where the formulas for $\epsilon_\ell$ and $dv_\ell$ hold for $\ell = 1, \dots, L-1$ and the one for $d\theta_\ell$ for $\ell = 1, \dots, L$; $\epsilon_L$ is held fixed. This applies to any differentiable loss.

**Claim 2 (fixed points equal backpropagation).** Under the fixed prediction assumption every fixed point of the inference dynamics satisfies

$$\epsilon^*_\ell = \delta_\ell = \frac{\partial \mathcal L(\hat y, y)}{\partial \hat v_\ell}, \qquad d\theta_\ell = -\frac{\partial \mathcal L(\hat y, y)}{\partial \theta_\ell}, \qquad \ell = 1, \dots, L.$$

**Claim 3 (hidden-layer precisions do not change learning).** Let $P_\ell = \Sigma_\ell^{-1}$ be symmetric precision matrices for the hidden layers and use precision-weighted errors $\tilde\epsilon_\ell = (\hat v_\ell - v_\ell) P_\ell$ in place of $\epsilon_\ell$ ($\ell < L$), with $\tilde\epsilon_L = \partial \mathcal L(\hat y, y)/\partial \hat y$. If the fixed point exists and is unique, then $\tilde\epsilon^*_\ell = \partial \mathcal L/\partial \hat v_\ell$ and $d\theta_\ell = -\partial \mathcal L/\partial \theta_\ell$, whatever the $P_\ell$. For the squared loss with an output precision, $\tilde\epsilon_L = (\hat v_L - y) P_L$, the fixed-point updates become $d\theta_\ell = -\frac{\partial \mathcal L}{\partial \hat y} P_L \frac{\partial \hat y}{\partial \theta_\ell}$: only the output precision re-weights the gradient.

## Expansion

Setting $dv_\ell = 0$ in either scheme gives the backward recursion $\epsilon^*_\ell = \epsilon^*_{\ell+1} J_{\ell+1}$, where $J_{\ell+1}$ is the Jacobian of $f_{\ell+1}$. Under the fixed prediction assumption $J_{\ell+1}$ is evaluated at the forward pass, where $\hat v_{\ell+1} = f_{\ell+1}(\hat v_\ell; \theta_{\ell+1})$ holds, so the chain rule collapses the product and the recursion is literally the backward pass started from the fixed $\epsilon_L = \delta_L$. In strict predictive coding the Jacobians are evaluated at relaxed beliefs that are not a forward pass, so the same recursion produces a different product. Precision weighting changes only the variable in which the recursion is written, not the recursion itself, which is why hidden-layer precisions drop out. The free energy $F$ is the negative log joint density of the Gaussian model up to constants, i.e. the variational free energy used in predictive coding accounts of cortex. The argument is a derivation for arbitrary differentiable layer maps; the source also shows numerically that strict predictive coding still learns on MNIST although its updates do not match the gradients (it failed to converge on the 6-layer CIFAR-10 model), and that strict updates with a step of $0.5$ or $1$ diverge.

## Sources

- R. Rosenbaum, "On the relationship between predictive coding and backpropagation", PLoS ONE 17(3) (2022) e0266102, Eqs (1)–(12) and the sections on strict predictive coding, the fixed prediction assumption, and precision matrices in hidden layers, <https://doi.org/10.1371/journal.pone.0266102>, PMCID PMC8970408.
