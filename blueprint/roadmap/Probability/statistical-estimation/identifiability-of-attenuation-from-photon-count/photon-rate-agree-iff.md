# With positive intensities, the transmitted rates agree iff $Ax = Ax'$

Let the rays be indexed by any set $\iota$ and the attenuation cells by a finite set $\kappa$, let
$A$ be a real $\iota \times \kappa$ matrix, and let each ray $j$ have a real source intensity
$I_{0,j} > 0$. For attenuation vectors $x, x' \in \mathbb{R}^{\kappa}$, the transmitted rates agree
in every ray,

$$I_{0,j}\, e^{-(Ax)_j} = I_{0,j}\, e^{-(Ax')_j} \quad \text{for all } j \in \iota,$$

if and only if $Ax = Ax'$, where $(Ax)_j = \sum_{k \in \kappa} A_{jk} x_k$. The positivity of each
intensity matters: in a ray with $I_{0,j} = 0$ both rates are $0$ whatever $(Ax)_j$ is. In the CT
reading, $A_{jk} \ge 0$ is the length of ray $j$ in cell $k$, $x_k \ge 0$ is the attenuation
coefficient of cell $k$, and $(Ax)_j$ is the line integral of attenuation along ray $j$; the
equivalence holds for all real $A$, $x$ and $x'$. Together with the fact that a product of Poisson
laws determines its rates, it gives the
[identification of the photon-count law](photon-law-agree-iff.md).
