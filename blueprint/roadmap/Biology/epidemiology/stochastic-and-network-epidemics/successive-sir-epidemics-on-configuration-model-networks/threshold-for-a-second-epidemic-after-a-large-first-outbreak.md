# Threshold for a second SIR epidemic after a large first outbreak in the coloured-tree approximation of a configuration-model network

**First epidemic.** Let $G_n$ be a configuration-model graph on $n$ vertices with i.i.d. degrees $D$, $p_k = \mathbb{P}(D = k)$, $\mathbb{E}[D^2] < \infty$, mean $\mu_D$, and size-biased degree $\tilde D$ with $\mathbb{P}(\tilde D = k) = kp_k/\mu_D$. An SIR epidemic with unit infectious period and contact rate $\beta$ along each edge infects each neighbour of an infective independently with probability $p = 1 - e^{-\beta}$. Its basic reproduction number is $R_0^{(1)} = p\,\mathbb{E}[\tilde D - 1]$. Let $\tilde q$ be the smallest root in $[0,1]$ of $s = \mathbb{E}[(1 - p + ps)^{\tilde D - 1}]$ and $q = \mathbb{E}[(1 - p + p\tilde q)^D]$; when $R_0^{(1)} > 1$, a large first outbreak occurs with asymptotic probability $1 - q$ and then infects a fraction $1 - q$ of the vertices.

**Second epidemic.** Conditional on a large first epidemic, a second SIR epidemic starts from one infective. Call a vertex a 1-vertex if it was infected in the first epidemic and a 0-vertex otherwise. An infected $i$-vertex has a fixed infectious period $\ell_i^{(2)}$ and makes infectious contacts with a given $j$-neighbour at rate $\beta_{ij}$, so it transmits to that neighbour with probability

$$
\pi_{ij} = 1 - e^{-\beta_{ij}\ell_i^{(2)}}, \qquad i,j \in \{0,1\}.
$$

This covers leaky partial immunity ($\pi_{00} = p'$, $\pi_{01} = \alpha_S p'$, $\pi_{10} = \alpha_I p'$, $\pi_{11} = \alpha_S\alpha_I p'$), complete cross-immunity ($\pi_{00} = p'$, other $\pi_{ij} = 0$), and spread only among previously infected vertices ($\pi_{11} = p'$, other $\pi_{ij} = 0$). Define

$$
\begin{aligned}
\mu_{AA} &= \sum_{k\ge2}(k-1)\tilde p_k\bigl(1 - (1-p)(1-p+p\tilde q)^{k-2}\bigr), &
\mu_{AB} &= \frac{\tilde q}{1-\tilde q}\sum_{k\ge2}(k-1)\tilde p_k\bigl(1 - (1-p+p\tilde q)^{k-2}\bigr),\\
\mu_{BA} &= \frac{(1-p)(1-\tilde q)}{\tilde q}\sum_{k\ge2}(k-1)\tilde p_k(1-p+p\tilde q)^{k-2}, &
\mu_{BB} &= \sum_{k\ge2}(k-1)\tilde p_k(1-p+p\tilde q)^{k-2},
\end{aligned}
$$

and the mean offspring matrix

$$
M = \begin{pmatrix}
\pi_{11}\mu_{AA} & p\,\pi_{11}\mu_{AB} & (1-p)\pi_{10}\mu_{AB}\\
\pi_{11}\mu_{BA} & p\,\pi_{11}\mu_{BB} & (1-p)\pi_{10}\mu_{BB}\\
\pi_{01}\mu_{BA} & 0 & \pi_{00}\mu_{BB}
\end{pmatrix}.
$$

**Statement.** Approximate the second epidemic, as $n \to \infty$, by the three-type branching process on the coloured approximating tree described below, whose mean offspring matrix is $M$, and let $R_0^{(2)}$ be the dominant eigenvalue of $M$. This branching process survives with strictly positive probability if and only if $R_0^{(2)} > 1$. The same holds under *polarized* partial immunity, in which each first-epidemic case independently regains full susceptibility with probability $\alpha$, with $\pi_{00} = \pi_{10} = p'$ and $\pi_{01} = \pi_{11} = \alpha p'$. If moreover $p' = p$ (the second disease equals the first apart from residual immunity), $R_0^{(2)}(\alpha)$ is continuous and strictly increasing in $\alpha$ with $R_0^{(2)}(1) = R_0^{(1)}$, and the critical value $\alpha_c = \inf\{\alpha : R_0^{(2)}(\alpha) > 1\} \in (0,1)$ is the smallest root in $[0,1]$ of

$$
p^3(1 - p\mu_{BB})(\mu_{AA}\mu_{BB} - \mu_{AB}\mu_{BA})\alpha^2 - p\bigl[(1 - p\mu_{BB})(\mu_{AA} + p\mu_{BB}) + p(1-p)\mu_{AB}\mu_{BA}\bigr]\alpha + 1 - p\mu_{BB} = 0 .
$$

## Depends on

- [Epidemic percolation network for SIR epidemics](../../epidemics-on-networks/kenah-robins-epidemic-percolation-network-exact-isomorphism-of-network.md)

## Proof sketch

With a constant infectious period the first epidemic is bond percolation with retention probability $p$, and its giant out-component is explored by a two-stage Galton–Watson tree. Locally, the graph around the initial case of the second epidemic is a two-stage Galton–Watson tree (root degree $D$, others $\tilde D$) whose edges are independently red (first-epidemic transmission) with probability $p$; a vertex was infected in the large first epidemic iff it lies on an infinite red path. Vertices are typed as (1) infected in the first epidemic and having an infinite red path of descent, (2) infected in the first epidemic without one, and (3) escaped the first epidemic. Label type 1 as $A$ and types 2–3 as $B$: a vertex has label $B$ with probability $\tilde q$, and Bayes' rule gives the conditional child-label laws, e.g. a label-$A$ vertex of degree $k$ has $\ell$ label-$A$ children with probability $\tilde p_k\binom{k-1}{\ell}(1-\tilde q)^\ell\tilde q^{k-1-\ell}\,\frac{1-(1-p)^\ell}{1-\tilde q}$. The $\mu_{ij}$ are the resulting mean numbers of label-$j$ children of a label-$i$ vertex, and splitting label-$B$ children by edge colour ($p$ or $1-p$) and multiplying by the second-epidemic transmission probabilities $\pi_{ij}$ gives $M$. The second epidemic is then approximated by a three-type branching process with mean matrix $M$, which survives with positive probability iff its Perron root exceeds $1$. The source proves these results for the coloured approximating tree and only argues heuristically that they carry over to the second epidemic on $G_n$ as $n \to \infty$; the statement above is therefore made for the tree.

## Sources

- Frank Ball, Abid Ali Lashari, David Sirl and Pieter Trapman, "Modelling the spread of two successive SIR epidemics on a configuration model network", *Journal of Mathematical Biology* 90 (2025), 51, <https://doi.org/10.1007/s00285-025-02207-y>. Preprint version: arXiv:2410.20889 (2024), Section 2, Theorems 1 and 4 and Lemma 1, <https://doi.org/10.48550/arXiv.2410.20889>.
