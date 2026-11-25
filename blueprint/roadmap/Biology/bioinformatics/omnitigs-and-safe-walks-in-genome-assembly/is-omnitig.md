# Omnitig

A sequence of edges $w = e_0, \dots, e_t$ is an omnitig if

- it is nonempty and is a [walk](is-walk.md), and
- for all $1 \le i \le j \le t$ there is no [path](is-path.md) $p$ from $\mathrm{src}(e_j)$ to $\mathrm{src}(e_i)$ whose first edge is not $e_j$ and whose last edge is not $e_{i-1}$

(Tomescu and Medvedev 2017, Definition 5).

## Sources

- A. I. Tomescu and P. Medvedev, *Safe and complete contig assembly through omnitigs*, J. Comput. Biol. 24 (2017), 590–602; arXiv:1601.02932, Definition 5.
