# Explicit infection profiles of the SIS model with recruitment for convex risk functions

Use the setting and notation of the [free-boundary limit of the diffusive SIS model with recruitment and disease death](free-boundary-limit-of-the-sis-model-with-recruitment-and-death.md): risk function $h = (\gamma + \eta)/\beta$, constant recruitment $\Lambda > h$ on $[0, L]$, limits $\hat S$ and $\mu$ of the endemic equilibria as $d_I \to 0$. Assume $h \in C^2([0, L])$.

**Theorem.**

1. *(Whole-habitat infection.)* If $-d_S h_{xx} \le \Lambda - h$ in $(0, L)$, $h_x(0) \ge 0$ and $h_x(L) \le 0$, then $\hat S = h$ on $[0, L]$ and

$$\frac{d\mu}{dx}(x) = \frac{\Lambda - h(x) + d_S h_{xx}(x)}{\eta(x)} \quad \text{for a.e. } x \in (0, L),$$

that is, $\mu$ restricted to $(0, L)$ is absolutely continuous with this density: $\mu(B) = \int_B (\Lambda - h + d_S h_{xx})/\eta \, dx$ for every Borel set $B \subset (0, L)$.

2. *(Neighbourhood of an interior minimum.)* If $h_x$ is non-decreasing on $[0, L]$ and $\Theta_h = \{\tau_0\}$ with $0 < \tau_0 < L$, then there are unique $0 < \tau_1 < \tau_0 < \tau_2 < L$ determined by

$$\tanh\Big(\frac{\tau_1}{\sqrt{d_S}}\Big) = -\frac{\sqrt{d_S}\, h_x(\tau_1)}{\Lambda - h(\tau_1)}, \qquad \tanh\Big(\frac{\tau_2 - L}{\sqrt{d_S}}\Big) = -\frac{\sqrt{d_S}\, h_x(\tau_2)}{\Lambda - h(\tau_2)},$$

such that $\hat S = h$ on $[\tau_1, \tau_2]$ and, on $(\tau_1, \tau_2)$, $\mu$ is absolutely continuous with the density $d\mu/dx$ of part 1; on $[0, \tau_1) \cup (\tau_2, L]$, $\hat S < h$ solves $-d_S \hat S_{xx} = \Lambda - \hat S$ with $\hat S_x(0) = \hat S_x(L) = 0$ and $\hat S(\tau_k) = h(\tau_k)$, and $\mu = 0$ there.
3. *(Boundary concentration.)* If $h_x$ is non-decreasing, $\Theta_h = \{L\}$ and $\tanh(L/\sqrt{d_S}) \le -\sqrt{d_S}\, h_x(L)/(\Lambda - h(L))$, then $\hat S$ is the unique positive solution of $-d_S \hat S_{xx} = \Lambda - \hat S$ on $(0, L)$, $\hat S_x(0) = 0$, $\hat S(L) = h(L)$, and the infection is a point mass at the boundary:

$$\mu([0, L)) = 0, \qquad \mu(\{L\}) = \frac{\Lambda L - \int_0^L \hat S\,dx}{\eta(L)}.$$

If instead the strict reverse inequality holds, the conclusions of part 2 hold with $[\tau_1, \tau_2]$ replaced by $[\tau_1, L]$, and $\mu([0, \tau_1)) = 0$. The case $\Theta_h = \{0\}$ is symmetric, and if $\Theta_h = [\varrho_1, \varrho_2]$ is an interior interval with $h_x$ non-decreasing off it, part 2 holds with $\tau_1 < \varrho_1 < \varrho_2 < \tau_2$.

So, unlike the conserved model, the disease can occupy a whole neighbourhood of the highest-risk point or even the whole habitat, and whether it concentrates at a boundary minimum depends on the slope $h_x$ there.

## Depends on

- [Free-boundary limit of the diffusive SIS model with recruitment and disease death](free-boundary-limit-of-the-sis-model-with-recruitment-and-death.md)

## Expansion

Off the contact set $\hat S$ solves the linear equation $-d_S \hat S_{xx} = \Lambda - \hat S$, so with a Neumann condition at $0$, $\hat S = \Lambda - A\cosh(x/\sqrt{d_S})$ on $[0, \tau_1]$. $C^1$ contact with $h$ at $\tau_1$ means $\Lambda - h(\tau_1) = A\cosh(\tau_1/\sqrt{d_S})$ and $h_x(\tau_1) = -A\sinh(\tau_1/\sqrt{d_S})/\sqrt{d_S}$; dividing gives the $\tanh$ equation, and monotonicity of $h_x$ makes its root unique. On the contact set $\hat S = h$, and the weak form of the free-boundary equation, tested against smooth functions supported in the interior of the contact set, yields the density $(\Lambda - h + d_S h_{xx})/\eta$ of $\mu$ with respect to Lebesgue measure there, which is nonnegative exactly under the hypothesis of part 1. (Testing the weak form of part 1 against all $\zeta \in W^{1,2}(0, L)$ and integrating by parts also shows that $\mu$ has atoms $\mu(\{0\}) = d_S h_x(0)/\eta(0)$ and $\mu(\{L\}) = -d_S h_x(L)/\eta(L)$ at the endpoints, both nonnegative under the slope hypotheses.) At a boundary minimum, if the $\tanh$ condition has no interior root, the contact set shrinks to $\{L\}$ and integrating the equation for $\hat S$ gives the mass of the Dirac component.

## Sources

- R. Peng, Z.-A. Wang, G. Zhang and M. Zhou, Novel spatial profiles of some diffusive SIS epidemic models, *J. Math. Biol.* (2023), <https://doi.org/10.1007/s00285-023-02013-4>; preprint arXiv:2301.01012. Journal version: Theorem 2.3 (i)-(iii), equations (2.9)-(2.21) (equations (2.15)-(2.27) in the arXiv preprint). The source writes $\mu(\{x\})$ for the density on the open interval; the weak formulation of Theorem 2.2 identifies it as $d\mu/dx$.
