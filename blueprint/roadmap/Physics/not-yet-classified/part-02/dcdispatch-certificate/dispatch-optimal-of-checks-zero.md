# Zero-gap dispatch certificate proves optimality

Consider a network with buses $v \in \{1, \dots, n_N\}$, branches $e$ from bus $\mathrm{tail}(e)$ to bus $\mathrm{head}(e)$ with rational susceptances $b_e$, generators $g$ located at buses $\mathrm{bus}(g)$, a reference bus $r$, and rational demands $d_v$, generator limits $p^{\min}_g, p^{\max}_g$, branch flow limits $f^{\min}_e, f^{\max}_e$ and costs $c_g$. Let $B$ be the incidence matrix ($B_{ve} = 1$ if $v = \mathrm{tail}(e)$, minus $1$ if $v = \mathrm{head}(e)$), $L = B \operatorname{diag}(b) B^{\mathsf T}$ the weighted Laplacian, $f(\theta) = \operatorname{diag}(b) B^{\mathsf T}\theta$ the branch flows, and $C$ the generator-to-bus incidence. A real dispatch $(p, \theta) \in \mathbb{R}^{n_G} \times \mathbb{R}^{n_N}$ is feasible when $L\theta = Cp - d$, $\theta_r = 0$, $p^{\min} \le p \le p^{\max}$ and $f^{\min} \le f(\theta) \le f^{\max}$ (all data read as reals); its cost is $c \cdot p$.

A certificate consists of a rational dispatch $(p, \theta)$, nodal prices $\lambda \in \mathbb{Q}^{n_N}$, a reference multiplier $\rho \in \mathbb{Q}$, generator bound multipliers $\mu^{\mathrm{hi}}, \mu^{\mathrm{lo}} \in \mathbb{Q}^{n_G}$, flow bound multipliers $\eta^{\mathrm{hi}}, \eta^{\mathrm{lo}} \in \mathbb{Q}^{n_E}$ and a budget $\varepsilon \in \mathbb{Q}$. Its certified lower bound is

$$\ell = d \cdot \lambda + p^{\min} \cdot \mu^{\mathrm{lo}} - p^{\max} \cdot \mu^{\mathrm{hi}} + f^{\min} \cdot \eta^{\mathrm{lo}} - f^{\max} \cdot \eta^{\mathrm{hi}}.$$

If the exact certificate checker accepts the certificate with budget $\varepsilon = 0$, then $(p, \theta)$ is feasible, $c \cdot p \le c \cdot p'$ for every feasible real dispatch $(p', \theta')$, and $c \cdot p = \ell$ (as rationals).
