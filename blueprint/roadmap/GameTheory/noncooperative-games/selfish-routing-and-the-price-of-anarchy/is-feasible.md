# Feasible flow for a demand vector

Let a nonatomic routing instance and a demand $r_i \in \mathbb R$ for every commodity $i$ be
given. A path flow $f : \mathcal P \to \mathbb R$ is feasible for $r$ if $f_P \ge 0$ for every
path $P$ and $\sum_{P : i(P) = i} f_P = r_i$ for every commodity $i$.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, §2.1.
