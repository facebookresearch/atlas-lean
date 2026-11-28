# Measurement selection for identifying SIR rates on a network

**Model.** On a weighted directed graph $\mathcal G=(\mathcal V,\mathcal E)$, $\mathcal V=[n]$, node $i$ carries susceptible, infected and recovered fractions $s_i[k],x_i[k],r_i[k]$ with $s_i+x_i+r_i=1$, evolving by the discrete-time networked SIR model

$$x_i[k+1]=(1-h\delta)x_i[k]+h\beta\,s_i[k]\sum_{j\in\bar{\mathcal N}_i}a_{ij}x_j[k],\qquad r_i[k+1]=r_i[k]+h\delta\,x_i[k],$$

with unknown infection rate $\beta>0$ and recovery rate $\delta>0$, known weights $a_{ij}>0$ on edges, sampling step $h>0$, $h\delta<1$ and $h\beta\sum_j a_{ij}<1$, and initial states $s_i[0]\in(0,1]$, $r_i[0]=0$.

**Identifiability as a rank condition.** Each update is linear in $(\beta,\delta)$:

$$\frac{x_i[k+1]-x_i[k]}{h}=\Phi^x_{k,i}\begin{pmatrix}\beta\\ \delta\end{pmatrix},\quad \frac{r_i[k+1]-r_i[k]}{h}=\Phi^r_{k,i}\begin{pmatrix}\beta\\ \delta\end{pmatrix},\quad \Phi^x_{k,i}=\Bigl(s_i[k]\sum_{j}a_{ij}x_j[k],\ -x_i[k]\Bigr),\ \Phi^r_{k,i}=(0,\ x_i[k]).$$

A measurement selection $\mathcal I$ is a set of tests $x_i[k]$ (cost $c_{k,i}$) and $r_i[k]$ (cost $b_{k,i}$) over a window $k\in[t_1,t_2]$. It identifies $(\beta,\delta)$ exactly from noiseless data iff the coefficient rows whose entries are determined by $\mathcal I$ (directly or after eliminating unmeasured quantities) can be combined into a rank-$2$ matrix, $r_{\max}(\mathcal I)=2$.

**Theorem.**

1. *(Exact identification.)* The problem of minimizing $c(\mathcal I)$ subject to $r_{\max}(\mathcal I)=2$ is NP-hard. Writing $d_i$ for the graph distance from the initially infected set, $x_i[k]>0$ exactly for $k\ge d_i$ and $r_i[k]>0$ exactly for $k>d_i$, so rank $2$ can be certified before measuring from the graph and the infection seed alone; a polynomial-time algorithm built on this gives a feasible selection with cost within a ratio of the optimum that depends only on the local measurement costs and neighborhood sizes.
2. *(Budgeted noisy estimation.)* With noisy measurements, choosing measurements under a budget $B$ to optimize a Bayesian estimation-error criterion is also NP-hard. It recasts as maximizing a set function under a knapsack constraint, and for the D-optimal (log-determinant) criterion $f_{Pd}$ the greedy algorithm returns $\mathcal Y^g$ with

$$f_{Pd}(\mathcal Y^g)\ \ge\ \tfrac12\bigl(1-e^{-1}\bigr)f_{Pd}(\mathcal Y^\star)-\Bigl(\frac{B}{c_{\min}}+\frac32\Bigr)\varepsilon,$$

where $\varepsilon$ bounds the error of evaluating $f_{Pd}$ and $c_{\min}$ is the smallest measurement cost; for the A-optimal (trace) criterion the guarantee degrades through submodularity ratios.

## Expansion

Positivity propagates along shortest paths from the seed set, which fixes exactly which coefficients $\Phi^x_{k,i},\Phi^r_{k,i}$ are nonzero; one $x$-equation at an infected node with a self-loop plus one $r$-equation already gives two independent rows, and the algorithm searches over such pairs. NP-hardness of both problems is by reduction from set-cover/knapsack-type problems in which choosing a test at node $i$ also requires paying for the neighbors' prevalences entering $\Phi^x_{k,i}$. The greedy bound extends the $\tfrac12(1-e^{-1})$ knapsack guarantee for submodular maximization to approximately evaluated, possibly nonsubmodular objectives.

## Sources

- Lintao Ye, Philip E. Paré, Shreyas Sundaram, "Parameter Estimation in Epidemic Spread Networks Using Limited Measurements", SIAM Journal on Control and Optimization 60 (2022), S49–S74, <https://doi.org/10.1137/20m1377801>. Published version of arXiv:2105.04750, cited next; locators there refer to the arXiv version.
- L. Ye, P. E. Paré, S. Sundaram, "Parameter Estimation in Epidemic Spread Networks Using Limited Measurements", arXiv:2105.04750 (2021), Section 2 (model and assumptions), Lemma 1, Section 3 (PIMS problem, rank condition, NP-hardness theorem and approximation algorithm with its performance proposition) and Section 4 (PEMS problem, NP-hardness and greedy guarantee). <https://doi.org/10.48550/arXiv.2105.04750>
