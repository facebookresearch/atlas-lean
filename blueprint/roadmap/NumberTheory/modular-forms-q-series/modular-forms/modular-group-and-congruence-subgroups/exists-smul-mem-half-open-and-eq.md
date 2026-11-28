# Fundamental domain of the modular group

Let

$$F = \{\tau \in \mathbb{H} : \operatorname{re}\tau \in [-\tfrac12, \tfrac12),\ |\tau| \ge 1,
  \text{ and } (\operatorname{re}\tau > 0 \Rightarrow |\tau| > 1)\},$$

with $\mathrm{SL}_2(\mathbb{Z})$ acting on the upper half-plane $\mathbb{H}$ by Möbius
transformations. For every $\tau \in \mathbb{H}$:

1. there is $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $\gamma\tau \in F$; and
2. for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, if $\tau \in F$ and $\gamma\tau \in F$, then
   $\gamma\tau = \tau$.

So every $\mathrm{SL}_2(\mathbb{Z})$-orbit in $\mathbb{H}$ contains exactly one point of $F$.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, Lecture 15, Lemma 15.10. Written out here is the reduction from Mathlib's closed fundamental domain `ModularGroup.fd`: existence moves a point of the closed domain on its boundary into $F$ by $T^{-1}$ or $S$, and uniqueness runs through Mathlib's classification `ModularGroup.cases_of_mem_fd_smul_mem_fd` of the elements $g$ with $z, gz$ both in the closed domain. The maximal-imaginary-part argument of the source is Mathlib's `ModularGroup.exists_smul_mem_fd`.
