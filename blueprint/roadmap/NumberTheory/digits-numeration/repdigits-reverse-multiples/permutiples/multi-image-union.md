# Multi-image union of a multiset of cycles

Let $n$ and $b$ be natural numbers and let $I$
be a multiset of vertex lists. Let $C_I$ be the multiset cycle union of $I$: the multiset sum,
over the lists in $I$, of their edges, where a nonempty list $[v_0, \dots, v_{r-1}]$ has the
edges $(v_0, v_1), \dots, (v_{r-2}, v_{r-1}), (v_{r-1}, v_0)$ and the empty list has none. The
multi-image union $\Delta_I$ is the multiset obtained by replacing each edge $e = (d_1, d_2)$ of
$C_I$, with its multiplicity, by the multi-edge $(c_1, c_2)$ of the $(n, b)$-Hoey-Sloane
multigraph that carries the label $e$: $c_1 = \lambda(d_1 + (b - n) d_2)$, where $\lambda$ is
the least non-negative residue modulo $b$ computed in the integers (the identity when $b = 0$),
and $c_2 = \lfloor (n d_2 - d_1 + c_1) / b \rfloor$ (taken to be $0$ when $b = 0$), with a
negative value of $c_1$ or $c_2$ replaced by $0$.

The labels are dropped, since they do not affect in- and out-degrees, connectivity or Eulerian
circuits.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Definition 7.
