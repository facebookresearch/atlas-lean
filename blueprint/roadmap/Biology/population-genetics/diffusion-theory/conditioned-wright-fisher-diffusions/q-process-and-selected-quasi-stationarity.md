# The Q-process and quasi-stationarity under selection

For the neutral Wright–Fisher diffusion without mutation, $L_0 = \frac12x(1 - x)\partial_x^2$, the function $h(x) = x(1 - x)$ is the first eigenfunction of the killed generator with eigenvalue $-1$, $L_0h = -h$. Griffiths, Jenkins and Spanò (2018, Section 3.2, equation (25)) show that the space-time transform by $e^th(x)$ turns the killed transition density $f_{0,0}$ into $f_{2,2}(x, y; t) = e^tf_{0,0}(x, y; t)\,y(1 - y)/(x(1 - x))$, the transition density of the Wright–Fisher diffusion with generator

$$\tfrac12x(1 - x)\partial_x^2 + (1 - 2x)\partial_x,$$

that is, with mutation parameters $\theta_1 = \theta_2 = 2$. This is the Q-process, the neutral diffusion conditioned never to be absorbed: the conditional law given survival up to a time $T$ converges as $T \to \infty$ to this $h$-transform, as in the general construction of Cattiaux, Collet, Lambert, Martínez, Méléard and San Martín (2009, Section 6). Its stationary law is the Beta$(2, 2)$ law with density $6x(1 - x)$. It differs from the quasi-stationary (Yaglom) law of the killed process, which Griffiths, Jenkins and Spanò (Section 2) obtain as proportional to the first orthogonal polynomial times the speed density, here the uniform law on $(0, 1)$: the stationary density of the Q-process is proportional to $h$ times the Yaglom density, in line with Cattiaux et al. (2009, Remark 6.3), where the stationary measure of the Q-process is absolutely continuous with respect to the quasi-stationary distribution and dominates it stochastically. With selection the same construction uses the first eigenfunction of the killed selected generator, the oblate spheroidal function of Song and Steinrücken (2012, Algorithm 1) for genic selection without mutation; Griffiths, Jenkins and Spanò (Section 1) describe the $h$-transform of the selected transition density conditioned on non-absorption through the first eigenvalue–eigenfunction pair, with the Yaglom density computed from the first eigenfunction.

## Depends on

- [Beta density as Wright's stationary density](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/beta-pdfreal-eq-wright-density.md)
- [Quasi-stationary law of the neutral Wright–Fisher diffusion](neutral-quasi-stationary-distribution.md)

## Expansion

1. The first eigenpair $(h, -1)$ of the neutral killed generator and the space-time $h$-transform.
2. The Q-process generator $\frac12x(1 - x)\partial_x^2 + (1 - 2x)\partial_x$ and its Beta$(2, 2)$ stationary law.
3. The uniform Yaglom limit and the product relation between the two invariant laws.
4. Conditioning on survival to time $T$ and the limit $T \to \infty$, from the spectral gap of the killed process.
5. Selection: positivity of the first eigenfunction of the killed selected generator, the selected Q-process, and its stationary law.

## Sources

- R. C. Griffiths, P. A. Jenkins and D. Spanò, Wright–Fisher diffusion bridges, Theor. Popul. Biol. 122 (2018), 67–77; Sections 1, 2 and 3.2 and equation (25) in the numbering of the arXiv version, arXiv:1703.00208v3. <https://doi.org/10.1016/j.tpb.2017.09.005>
- P. Cattiaux, P. Collet, A. Lambert, S. Martínez, S. Méléard and J. San Martín, Quasi-stationary distributions and diffusion models in population dynamics, Ann. Probab. 37 (2009), 1926–1969, Section 6 and Remark 6.3. <https://doi.org/10.1214/09-AOP451>
- S. Méléard and D. Villemonais, Quasi-stationary distributions and population processes, Probab. Surveys 9 (2012), 340–410. <https://doi.org/10.1214/11-PS191>
- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, Algorithm 1. <https://doi.org/10.1534/genetics.111.136929>
