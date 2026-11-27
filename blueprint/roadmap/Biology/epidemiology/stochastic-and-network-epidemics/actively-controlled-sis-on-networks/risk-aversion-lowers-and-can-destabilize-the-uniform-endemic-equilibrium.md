# Risk aversion lowers and can destabilize the uniform endemic equilibrium of network actSIS

**Setting.** Use the [network actSIS model](transcritical-onset-of-endemic-equilibria-in-the-network-actsis-model.md) with homogeneous parameters $\delta_j = \delta > 0$ and $\alpha_j = \alpha$ for all $j$, where $\alpha : [0,1] \to [0,1]$ is $C^1$. Call $\alpha$ a *risk-aversion strategy* if $\alpha'(p) < 0$ for all $p \in (0,1)$, i.e. populations cut contacts as perceived infection rises. A standard example is the saturating response

$$
\alpha_A(p) = \frac{\mu^\nu (1-p)^\nu}{p^\nu (1-\mu)^\nu + \mu^\nu (1-p)^\nu}, \qquad \mu \in (0,1),\ \nu > 1 .
$$

**Statement.**

1. *Well-mixed comparison.* For the well-mixed SIS model $\dot p = \bar\beta(1-p)p - \delta p$ and the well-mixed actSIS model with the same $\bar\beta > \delta$ and a risk-aversion strategy $\alpha$, the endemic infection levels satisfy $p^*_{\mathrm{SIS}} \ge p^*_{\mathrm{actSIS}}$.
2. *Uniform endemic equilibrium (UEE).* Let $A$ and $\hat A$ be adjacency matrices of connected regular graphs with degrees $d$ and $\hat d$. The network SIS model has the unique, globally stable endemic equilibrium $p^*_{\mathrm{SIS}}\mathbf 1$ with

$$
p^*_{\mathrm{SIS}} = 1 - \frac{\delta}{\bar\beta d},
$$

and the endemic equilibrium of network actSIS that bifurcates from the infection-free state is $(p^*\mathbf 1, p^*\mathbf 1)$, where $p^* = p^*_{\mathrm{actSIS}}$ solves

$$
\bar\beta d\,(1-p^*)\,\alpha(p^*) = \delta ;
$$

it exists for all $\bar\beta > \delta/d$.
3. *Risk aversion lowers the UEE.* If in addition $\alpha$ is a risk-aversion strategy and $\bar\beta > \delta/d$, then $p^*_{\mathrm{SIS}}\mathbf 1 \succeq p^*_{\mathrm{actSIS}}\mathbf 1$ componentwise.
4. *Loss of stability.* Define

$$
g(p) = -\delta p + (1-p)\left( \lambda_{\max}\!\left( \frac{1}{d}A + \frac{1}{\hat d}\,\frac{\alpha'(p)}{\alpha(p)}\, p\, \hat A \right) - 1 \right).
$$

If $g$ has a zero in $(0,1)$, let $p_2$ be the smallest one and $\bar\beta_2 = \delta/\bigl(d(1-p_2)\alpha(p_2)\bigr) > \bar\beta^*$. If $p_2$ is the unique zero, the UEE is unstable for all $\bar\beta > \bar\beta_2$. Otherwise it is locally exponentially stable for $\bar\beta^* < \bar\beta < \bar\beta_2$ and unstable for $\bar\beta \in (\bar\beta_2, \bar\beta_3)$, where $\bar\beta_3 = \delta/\bigl(d(1-p_3)\alpha(p_3)\bigr)$ for a zero $p_3 > p_2$ of $g$.

Thus, unlike network SIS, where the endemic equilibrium is unique and stable above threshold, the uniform state of network actSIS can lose stability. Numerically this happens when the communication graph is sparse (small $\hat d$), and the network then settles to a non-uniform endemic state in which some populations over- and others under-estimate the average risk.

## Depends on

- [Transcritical onset of endemic equilibria in the network actSIS model](transcritical-onset-of-endemic-equilibria-in-the-network-actsis-model.md)
- [For $R_0 > 1$, global asymptotic stability of the endemic equilibrium of the SIS model](../../sis-epidemic-model/endemic-globally-asymptotically-stable.md)

## Proof sketch

For items 1 and 3 interpolate between the models with $\gamma(p,s) = (1-s) + s\,\alpha(p)$, $s \in [0,1]$: the equilibrium equation $\bar\beta d\,\gamma(p^*,s)(1-p^*) = \delta$ (with $d = 1$ in the well-mixed case) gives SIS at $s = 0$ and actSIS at $s = 1$. Implicit differentiation yields

$$
\frac{dp^*}{ds} = \frac{(1-p^*)(1-\alpha(p^*))}{s\bigl(\alpha'(p^*)(1-p^*) + 1 - \alpha(p^*)\bigr) - 1},
$$

whose numerator is positive and whose denominator is negative whenever $\alpha' < 0$, so $p^*$ decreases from the SIS to the actSIS value. For item 4, at $(p^*\mathbf 1, p^*\mathbf 1)$ the equilibrium identity reduces the Jacobian to a $2\times2$ block matrix; Schur's determinant formula shows that the $\bar\beta$-dependent eigenvalues are those of $-\delta(1 + \bar\beta d p^*\alpha(p^*))I + \frac{\delta}{d}A + \frac{\delta}{\hat d}\frac{\alpha'(p^*)}{\alpha(p^*)}p^*\hat A$, whose largest eigenvalue equals $\delta g(p^*)/(1-p^*)$. Stability is therefore governed by the sign of $g$ along the equilibrium branch, and the crossings of zero give $\bar\beta_2$ and $\bar\beta_3$ through the equilibrium identity.

## Sources

- Anastasia Bizyaeva, Marcela Ordorica Arango, Yunxiu Zhou, Simon Levin and Naomi Ehrich Leonard, "Active Risk Aversion in SIS Epidemics on Networks", in *2024 American Control Conference (ACC)*, IEEE, 2024, 4428–4433, <https://doi.org/10.23919/acc60939.2024.10644997>. Preprint version: arXiv:2311.02204 (2023), Lemma V.1, Lemma V.2, Theorem V.3 and Theorem V.4, <https://doi.org/10.48550/arXiv.2311.02204>.
