# Time-delay Boolean networks with prerequisite and similarity relations

**Classical Boolean network.** Genes $v_1,\dots,v_n$ take states in $\{0,1\}$ (off/on). In a Boolean network each $v_i$ has input genes $v_{i_1},\dots,v_{i_k}$ and a Boolean function $f_i$ with $v_i(t+1) = f_i\big(v_{i_1}(t),\dots,v_{i_k}(t)\big)$. Writing $v_i'$ for the state at $t+1$, each sample is an input/output pair (expression profile at $t$, profile at $t+1$).

**Time-delay relations.** Let $g = g(x_{i_1},\dots,x_{i_k})$ be a Boolean function of input genes and $z$ a target gene, with $\bar z$ its dual ($1-z$).

- *Prerequisite*, $g \prec z$: the on-status of $g$ at time $t$ is necessary for the on-status of $z$ at time $t+1$. If $g(t) = 0$ then $z(t+1) = 0$, while $g(t) = 1$ allows either output, which models a delayed effect.
- *Similarity*, $g \sim z$: $z(t+1) = g(t)$, the classical deterministic rule.

For each target the admissible relations are $g\prec z$, $g\prec\bar z$ and $g\sim z$: a prerequisite or similarity involving $\bar g$ can be rewritten with another Boolean function in place of $g$. If both $g_1 \prec z$ and $g_2 \prec \bar z$ hold and $g_2 = \bar g_1$, the two combine to $g_1 \sim z$. A time-delay Boolean network is therefore non-deterministic: an input state may have several possible outputs.

**Noise-free identification (indegree $2$).** For target $v_i$ and each input pair $(v_j, v_h)$, tabulate the counts $m_{abc}$ of samples with $(v_j, v_h, v_i') = (a, b, c)$ and mark cells positive or zero. Each of the eight basic relations $(v_j \text{ or } v_h)\prec v_i'$, $(\bar v_j \text{ or } v_h)\prec v_i'$, $\dots$, $(\bar v_j\text{ or }\bar v_h)\prec \bar v_i'$ forbids exactly one cell, namely the input $(a,b)$ that makes the clause false paired with output $c = 1$ (or $c = 0$ for $\bar v_i'$). A relation is consistent if its forbidden cell has count $0$; several consistent relations toward the same output are combined with "and" into one prerequisite function.

**Noisy data and the $p$-score.** Assume every input bit $I_{ij}$ and output bit $O_{ij}$ is flipped independently with misclassification probability $p$:

$$I_{ij}^* = \begin{cases} I_{ij} & \text{w.p. } 1-p,\\ 1 - I_{ij} & \text{w.p. } p,\end{cases}\qquad O_{ij}^* = \begin{cases} O_{ij} & \text{w.p. } 1-p,\\ 1 - O_{ij} & \text{w.p. } p.\end{cases}$$

The true triple counts $(m_{000},\dots,m_{111})$ are multinomial with cell probabilities $q_{i_1i_2i_3}$, and a true cell $i_1i_2i_3$ is observed as cell $j_1j_2j_3$ with probability

$$q_{i_1i_2i_3,\,j_1j_2j_3} = p^{I(i,j)}(1-p)^{3 - I(i,j)}\,q_{i_1i_2i_3}, \qquad I(i,j) = \sum_{k=1}^{3}|i_k - j_k| .$$

The observed counts are $n_{j_1j_2j_3} = \sum_{i}m_{i_1i_2i_3,\,j_1j_2j_3}$, the complete-data log-likelihood is

$$L = \sum_{i_1,i_2,i_3,j_1,j_2,j_3 = 0,1} m_{i_1i_2i_3,\,j_1j_2j_3}\log q_{i_1i_2i_3,\,j_1j_2j_3},$$

and the E-step imputes the split counts

$$\mathbb E\big(m_{i_1i_2i_3,\,j_1j_2j_3}\mid n_{j_1j_2j_3}\big) = \frac{n_{j_1j_2j_3}\,q_{i_1i_2i_3,\,j_1j_2j_3}}{\sum_{i'_1i'_2i'_3 = 0,1} q_{i'_1i'_2i'_3,\,j_1j_2j_3}} .$$

Under each of the eight hypotheses $q_{abc} = 0$ (one per basic relation), EM gives the maximum likelihood estimate of $p$. That estimate is the relation's *$p$-score*: the smaller it is, the better the relation explains the data. Relations with scores under a threshold are kept, and the threshold is chosen by maximum compatibility (the largest threshold whose kept relations contain no conflict).

## Expansion

Requiring every regulated gene to respond at the next time step is the main criticism of deterministic Boolean networks. A prerequisite relation keeps the logical structure of a Boolean rule but makes only the "off" implication certain, so it covers delayed and context-dependent activation as well as the classical rule (two opposite prerequisites with dual functions give a similarity). Restricting the search to indegree $2$ makes the candidate set polynomial: $\binom{n}{2}$ input pairs per target, eight basic hypotheses each.

The misclassification model treats binarized microarray calls as noisy. Each zero-cell hypothesis can only be reconciled with data that fall in its forbidden cell by attributing them to flips, so a true relation yields a small fitted $p$ and a false one a large $p$. On $100$ samples simulated from a three-gene network with $p = 0.05$, the first conflict appeared at threshold $0.138$, and the relations scoring below it reconstructed the generating network exactly. On $41$ yeast expression experiments the reconstructed Cat8 gluconeogenesis pathway agreed with the known regulation.

## Sources

- T.-H. Chueh, H. H.-S. Lu, "Inference of biological pathway from gene expression profiles by time delay boolean networks", PLoS ONE 7(8) (2012) e42095, sections Boolean Network, The Structure of Time Delay Boolean Network, Identification Algorithm and Identification Algorithm with Noisy Array: Equations (1)-(5) and Tables 1-5, <https://doi.org/10.1371/journal.pone.0042095>, PMCID PMC3432056.
