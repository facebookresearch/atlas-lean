# Reachability for piecewise-constant derivative systems is undecidable from dimension three

For deterministic dynamical systems on Euclidean space whose velocity is constant on each region of a finite polyhedral partition, the reachability problem is undecidable as soon as there are three variables, while it is decidable in the plane.

**Piecewise-constant derivative systems.** A piecewise-constant derivative (PCD) system on $\mathbb R^n$ is given by a partition of $\mathbb R^n$ into finitely many regions, each defined by linear inequalities, and a constant rate vector for each region. A trajectory moves with the rate vector of the region it is in and changes direction when it crosses into another region; there is no nondeterminism.

**Theorem (Asarin, Maler and Pnueli).** The reachability problem for PCD systems with three or more variables is undecidable. For two-dimensional PCD systems it is decidable.

## Depends on

None.

## Proof depends on

None.

## Expansion

The undecidability proof, a simulation of computation by three-dimensional PCD systems, is in the original paper and is not reproduced in the survey read; it has no page here. Asarin and Maler later observed that, because PCD systems can make Zeno runs, every set of the arithmetical hierarchy is recognized by a PCD system of some finite dimension. The decidability in dimension two was extended to piecewise-Hamiltonian systems by Cerans and Viksna and to simple planar differential inclusions by Asarin, Schneider and Yovine.

## Sources

- Eugene Asarin, Oded Maler and Amir Pnueli, "Reachability analysis of dynamical systems having piecewise-constant derivatives", *Theoretical Computer Science* 138(1), 1995, pp. 35–65, <https://doi.org/10.1016/0304-3975(94)00228-B> (cited after the survey below).
- Eugene Asarin and Oded Maler, "Achilles and the tortoise climbing up the arithmetical hierarchy", *Journal of Computer and System Sciences* 57(3), 1998, pp. 389–398, <https://doi.org/10.1006/jcss.1998.1601> (cited after the survey below, for the arithmetical hierarchy remark).
- Shankara Narayanan Krishna and Ashutosh Trivedi, "Hybrid automata for formal modeling and verification of cyber-physical systems", *Journal of the Indian Institute of Science* 93(3), 2013 (special issue on cyber-physical systems); read as arXiv:1503.04928v1, <https://arxiv.org/abs/1503.04928v1>: Section IV-C ("Piecewise-constant derivative systems and their variants") of that version.
