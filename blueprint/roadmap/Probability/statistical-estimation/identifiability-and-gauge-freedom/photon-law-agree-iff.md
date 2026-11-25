# With positive intensities, the photon-count laws agree iff $Ax = Ax'$

Let the rays and the attenuation cells form finite sets, let $A$ be a real matrix indexed by rays
and cells, and let every source intensity be positive, $I_{0,j} > 0$. For attenuation vectors $x$
and $x'$, the [photon-count laws](photon-law.md) at $x$ and at $x'$ (products of Poisson laws with
means $I_{0,j} e^{-(Ax)_j}$ and $I_{0,j} e^{-(Ax')_j}$) are equal if and only if $Ax = Ax'$. So the
law of the counts determines the projections $Ax$, and nothing more about $x$. The positivity of the
intensities matters: a ray with $I_{0,j} = 0$ records $0$ photons almost surely, whatever $(Ax)_j$
is. In the CT reading, $A_{jk} \ge 0$ is the length of ray $j$ in cell $k$ and $x_k \ge 0$ the
attenuation coefficient of cell $k$; the equivalence holds for all real $A$, $x$ and $x'$.
