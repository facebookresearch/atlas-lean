# State matrix of the zone thermal network

Let `ι` be a finite index set of zones with decidable equality, with capacities `C i`, inter-zone
conductances `G i j` and boundary conductances `g0 i`. The state matrix has entries

`A i j = (G i j - [i = j] (∑_k G i k + g0 i)) / C i`,

where `[i = j]` is `1` on the diagonal and `0` off it: row `i` is zone equation `i` without its
input terms, divided by `C i`, and the self-conductance `G i i` cancels. It is meant for `C i > 0`;
with `x/0 = 0` row `i` is zero when `C i = 0`. Without self-links (`G i i = 0`), the matrix in
brackets is the negative of the
[stiffness matrix](../../classical-mechanics/particles-and-oscillations/harmonic-oscillators-equilibrium-and-spring-netw/stiffness-matrix.md)
of `G` and `g0`, which has `∑_k G i k + g0 i` on the diagonal and `-G i j` off it.
