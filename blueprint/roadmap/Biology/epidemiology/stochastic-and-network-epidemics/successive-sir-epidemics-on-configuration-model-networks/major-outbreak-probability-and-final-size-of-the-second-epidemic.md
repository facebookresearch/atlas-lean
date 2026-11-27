# Major-outbreak probability and final size of a second SIR epidemic in the coloured-tree approximation of a configuration-model network

**Setting.** Use the notation of the [threshold for a second epidemic](threshold-for-a-second-epidemic-after-a-large-first-outbreak.md): configuration-model degrees $D$ with probability generating function $f_D$, size-biased degree $\tilde D$, first-epidemic transmission probability $p$, quantities $\tilde q, q$, and second-epidemic transmission probabilities $\pi_{ij}$ from an $i$-vertex to a $j$-neighbour ($1$ = infected in the first epidemic, $0$ = not). Assume a large first epidemic and $R_0^{(2)} > 1$. For $\mathbf s = (s_1,s_2,s_3) \in [0,1]^3$ define the offspring generating functions of the three vertex types,

$$
\begin{aligned}
f_{\tilde{\mathbf Y}_1}(\mathbf s) &= \tfrac{1}{1-\tilde q}\Bigl[f_{\tilde D-1}\bigl((1-\tilde q)s_1 + \tilde q(ps_2 + (1-p)s_3)\bigr) - f_{\tilde D-1}\bigl((1-p)(1-\tilde q)s_1 + \tilde q(ps_2 + (1-p)s_3)\bigr)\Bigr],\\
f_{\tilde{\mathbf Y}_2}(\mathbf s) &= \tfrac{1}{\tilde q}\, f_{\tilde D-1}\bigl((1-p)(1-\tilde q)s_1 + \tilde q(ps_2 + (1-p)s_3)\bigr), \qquad
f_{\tilde{\mathbf Y}_3}(\mathbf s) = \tfrac{1}{\tilde q}\, f_{\tilde D-1}\bigl((1-p)(1-\tilde q)s_1 + \tilde q s_3\bigr),
\end{aligned}
$$

and their root versions $f_{\mathbf Y_1}$, $f_{\mathbf Y_3}$, obtained by replacing $f_{\tilde D-1}$ with $f_D$ and the prefactors $1/(1-\tilde q)$, $1/\tilde q$ with $1/(1-q)$, $1/q$. Thin each child by its transmission probability: with $t_{ij}(s) = 1 - \pi_{11} + \pi_{11}s$ for $i,j \in \{1,2\}$, $t_{i3}(s) = 1 - \pi_{10} + \pi_{10}s$, $t_{31}(s) = 1 - \pi_{01} + \pi_{01}s$, $t_{32} \equiv 0$, $t_{33}(s) = 1 - \pi_{00} + \pi_{00}s$, set $\tilde f_i(\mathbf s) = f_{\tilde{\mathbf Y}_i}(t_{i1}(s_1), t_{i2}(s_2), t_{i3}(s_3))$ and $f_i(\mathbf s) = f_{\mathbf Y_i}(t_{i1}(s_1), t_{i2}(s_2), t_{i3}(s_3))$. Let $\hat t_{ij}$ be the same maps with $\pi_{10}$ and $\pi_{01}$ interchanged (the backward, susceptibility-set direction), and define $\hat f_i$, $\check f_i$ from $f_{\tilde{\mathbf Y}_i}$, $f_{\mathbf Y_i}$ in the same way.

**Statement.** For the second epidemic on the coloured approximating tree, as in the threshold page:

1. *Probability of a major second outbreak.* Let $\boldsymbol\xi$ be the unique solution in $[0,1)^3$ of $\xi_i = \tilde f_i(\boldsymbol\xi)$, $i = 1,2,3$. If the initial infective is chosen uniformly at random, the forward three-type branching process survives with probability

$$
1 - q\,f_1(\boldsymbol\xi) - (1-q)\,f_3(\boldsymbol\xi);
$$

more precisely $1 - f_1(\boldsymbol\xi)$ if the initial infective was infected in the first epidemic and $1 - f_3(\boldsymbol\xi)$ if not.
2. *Final size.* Let $\hat{\boldsymbol\xi}$ be the unique solution in $[0,1)^3$ of $\hat\xi_i = \hat f_i(\hat{\boldsymbol\xi})$. The backward (susceptibility-set) three-type branching process from a uniformly chosen root survives with probability

$$
1 - q\,\check f_1(\hat{\boldsymbol\xi}) - (1-q)\,\check f_3(\hat{\boldsymbol\xi}).
$$

3. Under polarized partial immunity (each first-epidemic case independently regains susceptibility with probability $\alpha$; $\pi_{00} = \pi_{10} = p'$, $\pi_{01} = \pi_{11} = \alpha p'$), item 1 holds unchanged, and item 2 holds after replacing, for $i \in \{1,2\}$, $\hat f_i(\mathbf s) = 1 - \alpha + \alpha f_{\tilde{\mathbf Y}_i}(1 - p' + p's_1, 1 - p' + p's_2, 1 - p' + p's_3)$ and $\hat f_3(\mathbf s) = f_{\tilde{\mathbf Y}_3}(1 - p' + p's_1, 1 - p' + p's_2, 1 - p' + p's_3)$, and analogously $\check f_1, \check f_3$ with $f_{\mathbf Y_1}, f_{\mathbf Y_3}$. These survival probabilities are the source's approximations to the probability of a major second outbreak on $G_n$ and to the fraction of vertices it infects; the source justifies that transfer only heuristically. The correction in item 3 is needed because once the second epidemic is established, contacts with the same previously infected vertex are not independent: its immunity status is a single coin flip.

## Depends on

- [Threshold for a second SIR epidemic after a large first outbreak in the coloured-tree approximation of a configuration-model network](threshold-for-a-second-epidemic-after-a-large-first-outbreak.md)

## Proof sketch

The forward process of the second epidemic on the coloured tree is a three-type Galton–Watson process; its extinction probabilities from non-root types solve the fixed-point system $\boldsymbol\xi = \tilde{\mathbf f}(\boldsymbol\xi)$, whose solution in $[0,1)^3$ is unique when $R_0^{(2)} > 1$, and the root's extinction probability averages $f_1$ and $f_3$ over whether the root was in the first epidemic's giant component (probability $1-q$). For the final size, a vertex escapes a major outbreak iff its susceptibility set (the set of vertices that would infect it, explored backwards) is finite. The backward exploration is again a three-type branching process, with transmission probabilities reversed, $\pi_{ij} \to \pi_{ji}$, which explains the swap of $\pi_{10}$ and $\pi_{01}$ in $\hat t_{ij}$. Its non-extinction probability, averaged over the root's type, gives the final size; the fraction of first-epidemic cases reinfected is $1 - \hat\xi_1$ and of first-epidemic escapees infected is $1 - \hat\xi_3$.

## Sources

- Frank Ball, Abid Ali Lashari, David Sirl and Pieter Trapman, "Modelling the spread of two successive SIR epidemics on a configuration model network", *Journal of Mathematical Biology* 90 (2025), 51, <https://doi.org/10.1007/s00285-025-02207-y>. Preprint version: arXiv:2410.20889 (2024), Section 3, Theorems 2, 3 and 4, <https://doi.org/10.48550/arXiv.2410.20889>.
