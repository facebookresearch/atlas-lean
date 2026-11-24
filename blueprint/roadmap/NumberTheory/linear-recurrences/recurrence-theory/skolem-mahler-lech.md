# Skolem–Mahler–Lech theorem

Let $K$ be a field of characteristic zero, let $k$ be a
natural number, let $c_0, \dots, c_{k-1} \in K$, and let $u_0, u_1, u_2, \dots$ be a sequence in
$K$ satisfying the linear recurrence $u_{n+k} = \sum_{i=0}^{k-1} c_i u_{n+i}$ for all $n \ge 0$
(for $k = 0$ the sum is empty and every $u_n$ is $0$). Then there are a finite set
$F \subseteq \mathbb{N}$ and finitely many pairs $(a_1, d_1), \dots, (a_m, d_m)$ of natural numbers
with every $d_j > 0$ such that the zero set of the sequence is

$$\{n \in \mathbb{N} : u_n = 0\} = F \cup \bigcup_{j=1}^{m} \{a_j + d_j t : t \in \mathbb{N}\}.$$

The proof follows Lech's $p$-adic method: the data embed in $\mathbb{Z}_p$ for a suitable prime $p$
(a Cassels-type embedding), on each residue class modulo the period of the companion matrix
modulo $p$ the sequence is given by a convergent $p$-adic power series, and Strassmann's theorem
bounds its zeros. C. Lech, A note on recurring series, Ark. Mat. 2 (1953), 417–421;
J. W. S. Cassels, An embedding theorem for fields, Bull. Austral. Math. Soc. 14 (1976), 193–198.

## Sources

- https://en.wikipedia.org/wiki/Skolem%E2%80%93Mahler%E2%80%93Lech_theorem (statement id `skolem-lech-s1`).
