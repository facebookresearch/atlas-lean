# Support of an elementary mode determines it up to scaling

**Rank criterion for extreme rays.** Let $P(A) = \{ x \in \mathbb{R}^d : A x \ge 0 \}$ be a pointed
polyhedral cone ($\operatorname{rank} A = d$), and for a ray $r$ let $A_{Z(r)}$ be the submatrix of the
rows of $A$ that are active at $r$. Then

$$r \text{ is an extreme ray of } P(A) \iff \operatorname{rank}\bigl(A_{Z(r)}\bigr) = d - 1 .$$

**Consequence for elementary modes.** Let $N \in \mathbb{R}^{m \times q}$ be the stoichiometric matrix
of a network in which every reaction is irreversible (reversible reactions split into two), and let
$e$ be an elementary mode with support $R(e) = \{ i : e_i \ne 0 \}$. Write $N_{R(e)}$ for the
$m \times |R(e)|$ submatrix of the columns in $R(e)$. Then the homogeneous system

$$N_{R(e)}\, x = 0, \qquad x \in \mathbb{R}^{|R(e)|},$$

has a one-dimensional solution space, spanned by the restriction of $e$ to its support. Hence the
binary support pattern of an EM already determines the EM up to a positive factor.

**Maximal pathway length.** If $\operatorname{rank} N = m$, every elementary mode satisfies

$$|R(e)| \le m + 1 ,$$

because the extreme ray $e$ makes $q - 1$ linearly independent constraints active, of which at most
$m$ come from $N e = 0$, so at least $q - 1 - m$ sign constraints $e_i \ge 0$ hold with equality.

## Depends on

- [Elementary modes are the extreme rays of the split flux cone](elementary-modes-are-extreme-rays-of-the-split-flux-cone.md)

## Expansion

The rank criterion says that an extreme ray is cut out, up to scaling, by its active constraints:
the solution set of $A_{Z(r)} x = 0$ is a line. For the flux cone, the active constraints at $e$ are
the $m$ steady-state equations together with $x_i = 0$ for $i \notin R(e)$; eliminating the zero
coordinates leaves $N_{R(e)} x = 0$, whose null space must therefore be one-dimensional. This is what
makes the binary null-space algorithm work: the double description iterations are run on bit
patterns only (the adjacency test needs only zero sets), and the real-valued modes are recovered at
the end by solving one small null-space problem per pattern, which saves most of the memory of
storing floating-point tableaux. The bound $m + 1$ is used as a shortcut in the adjacency test,
since a candidate with fewer than $q - 1 - m$ zeros cannot be extreme.

## Sources

- J. Gagneur, S. Klamt, "Computation of elementary modes: a unifying framework and the new binary
  approach", BMC Bioinformatics 5 (2004) 175, Lemma 2, Eq. (14) and Eq. (15),
  <https://doi.org/10.1186/1471-2105-5-175> (PMC544875).
