# Agreement hypergraphs and reduced intersection matrices

Let $A_1, \dots, A_t \subseteq [n]$ and fix $k$. The *intersection matrix* $M_{A,k}(\alpha)$ is the matrix of the linear map

$$
(g_2, \dots, g_t) \mapsto \Big( \big(g_j(\alpha_i)\big)_{j \ge 2,\ i \in A_1 \cap A_j},\ \big(g_j(\alpha_i) - g_{j'}(\alpha_i)\big)_{2 \le j < j',\ i \in A_j \cap A_{j'}} \Big)
$$

on $(\mathbb{F}[x]_{<k})^{t-1}$. If polynomials $f_1, \dots, f_t$ of degree $< k$ agree with a common word $y$ on $A_1, \dots, A_t$, then $g_j = f_j - f_1$ lies in the kernel, so full column rank of $M_{A,k}(\alpha)$ forces $f_1 = \cdots = f_t$. The hypergraph $(A_1, \dots, A_t)$ is *$k$-weakly partition connected* if for every partition $\mathcal{P}$ of $[t]$,

$$
\sum_{i \in [n]} \big( \#\{P \in \mathcal{P} : P \cap \{j : i \in A_j\} \ne \emptyset\} - 1 \big)_{+} \ \ge\ k\,(|\mathcal{P}| - 1) .
$$

## Depends on

- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Sources

- Zeyu Guo, Zihan Zhang, "Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets", FOCS (2023); arXiv:2304.01403.
- Omar Alrabiah, Venkatesan Guruswami, Ray Li, "Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields", STOC (2024); arXiv:2304.09445.
