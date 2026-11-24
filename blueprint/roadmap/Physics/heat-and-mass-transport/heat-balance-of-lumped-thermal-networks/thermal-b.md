# Input matrix of the zone thermal network

Let `ι` be a finite index set of zones with decidable equality, with capacities `C i`, inter-zone
conductances `G i j` and boundary conductances `g0 i`. The input matrix acts on inputs `(Tout, P)`,
the outside temperature and the zone heating powers: the outside temperature enters zone `i` with
gain `g0 i / C i`, and the heating power of zone `j` enters zone `j` alone, with gain `1/C j`. It is
meant for `C i > 0`; with `x/0 = 0` row `i` is zero when `C i = 0`.
