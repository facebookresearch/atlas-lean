# Valleys following a run

Let $R = ((b_0, m_0), \dots, (b_{k-1}, m_{k-1}))$ be a list of
pairs of a Boolean letter and a natural number, read as the maximal runs of a block word in which
the letter $\mathrm{false}$ stands for a $0$-valley $DU$. For $i \in \mathbb{N}$, the number of
$0$-valleys immediately after run $i$ is $m_{i+1}$ if $i + 1 < k$ and $b_{i+1} = \mathrm{false}$,
and $0$ otherwise.

## Sources

- Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.3.2, Section 3 (`vᵢ` after `pᵢ`).
