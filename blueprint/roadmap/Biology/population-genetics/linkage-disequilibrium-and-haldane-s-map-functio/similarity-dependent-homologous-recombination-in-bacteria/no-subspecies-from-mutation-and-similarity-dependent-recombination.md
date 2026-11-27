# No subspecies emerge from mutation and similarity-dependent recombination in infinite bacterial populations

**Model.** Genomes are words $x=(x_1,\dots,x_n)$ over a finite alphabet $K$, with sites $\Lambda=\{1,\dots,n\}$; the population is a probability measure $\mu_\Lambda$ on $X=K^n$ (infinite population, no genetic drift). At site $i$ letter $a$ mutates to $b$ at rate $\alpha_i(a,b)$, each site's mutation matrix being irreducible. Homologous recombination on any subset $I\subseteq\Lambda$ replaces the substring $x_I$ by the substring $y_I$ of a randomly met genome, at rate $\varkappa\,\varphi(x_I,y_I)\,\mu_I(y_I)$, where $\mu_I$ is the marginal law of the substring on $I$ and $\varphi\ge0$ is a **symmetric** similarity function ($\varphi(x_I,y_I)=\varphi(y_I,x_I)$), so that similar sequences recombine more readily. The law evolves by the nonlinear (McKean) forward equation

$$\frac{d\mu_\Lambda(x)}{dt}=\sum_i\sum_{y_i}\bigl(\alpha_i(y_i,x_i)\mu_\Lambda(x_{\Lambda\setminus i},y_i)-\alpha_i(x_i,y_i)\mu_\Lambda(x)\bigr)+\varkappa\sum_I\sum_{y_I}\bigl(\varphi(y_I,x_I)\mu_I(x_I)\mu_\Lambda(x_{\Lambda\setminus I},y_I)-\varphi(x_I,y_I)\mu_I(y_I)\mu_\Lambda(x)\bigr),$$

which is the exact large-population limit of the corresponding individual-based model.

**Theorem.** The equation has a unique fixed point $q_\Lambda$, namely the stationary distribution of the pure mutation process (the product over sites of the stationary laws of the single-site mutation chains), and every trajectory satisfies $\mu_\Lambda(t)\to q_\Lambda$ as $t\to\infty$, for all mutation and recombination intensities and all initial distributions.

Consequently, in a finite population of $N$ bacteria at stationarity the genome frequencies converge in probability to $q_\Lambda$ as $N\to\infty$, and sampled genomes are asymptotically independent: similarity-dependent homologous recombination alone cannot split an infinite population into stable subspecies; any clustering must come from drift, selection or other asymmetries.

## Expansion

The Lyapunov function is the relative entropy $H(\mu_\Lambda\,\|\,q_\Lambda)=\sum_x\mu_\Lambda(x)\ln\bigl(\mu_\Lambda(x)/q_\Lambda(x)\bigr)$. For a finite stochastic matrix $P$ with an invariant positive measure $\hat\mu$, relative entropy to $\hat\mu$ cannot increase under $\mu\mapsto\mu P$. Over a short time $dt$, mutation is a linear Markov step with invariant law $q_\Lambda$, so it does not increase $H(\cdot\,\|\,q_\Lambda)$. Recombination on $I$, for the current $\mu$ frozen, is a linear Markov step whose invariant law is the product $\mu_{\Lambda\setminus I}\otimes\mu_I$ (this uses the symmetry of $\varphi$) and which preserves both marginals; combining the entropy inequality for this step with the chain rule for relative entropy and the product form of $q_\Lambda$ shows that recombination does not increase $H(\cdot\,\|\,q_\Lambda)$ either. Hence $H$ is non-increasing along trajectories, and a LaSalle argument, using irreducibility of mutation to show that $H$ strictly decreases unless $\mu=q_\Lambda$, yields uniqueness of the fixed point and global convergence.

## Sources

- S. A. Pirogov, A. N. Rybko, A. S. Kalinina, M. S. Gelfand, "Recombination processes and non-linear Markov chains", *Journal of Computational Biology* 23 (2016), 711–717, <https://doi.org/10.1089/cmb.2016.0051>; preprint arXiv:1312.7653, <https://doi.org/10.48550/arXiv.1312.7653>. Numbering of the arXiv version: Section 2 (model, nonlinear equation, the main theorem and the entropy lemmas).
