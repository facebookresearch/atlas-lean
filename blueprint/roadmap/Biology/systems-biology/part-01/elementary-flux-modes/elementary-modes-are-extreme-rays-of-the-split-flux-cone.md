# Elementary modes are the extreme rays of the split flux cone

**Setting.** A metabolic network has $m$ internal metabolites and $q$ reactions, with stoichiometric
matrix $N \in \mathbb{R}^{m \times q}$ (negative entries for educts, positive for products). The
reaction indices split into irreversible ones $\mathrm{Irrev}$ and reversible ones $\mathrm{Rev}$.
The steady-state flux cone is

$$P = \{ v \in \mathbb{R}^q : N v = 0,\ v_i \ge 0 \ (i \in \mathrm{Irrev}) \},$$

a convex polyhedral cone. For $v \in \mathbb{R}^q$ write $R(v) = \{ i : v_i \neq 0 \}$ for its support
and $v \simeq v'$ when $v = \alpha v'$ for some $\alpha > 0$. A vector $e \in P \setminus \{0\}$ is an
**elementary mode** (EM) if no $e' \in P \setminus \{0\}$ with $R(e') \subseteq R(e)$ exists other than
$e' \simeq e$ (support minimality).

**Pointed cones and extreme rays.** A cone $P(A) = \{ x \in \mathbb{R}^d : A x \ge 0 \}$ with
$\operatorname{rank} A = d$ is a pointed polyhedral cone. For $x \in P(A)$ let
$Z(x) = \{ i : A_{i\bullet} x = 0 \}$ be its zero (active) set. A ray $r$ of $P(A)$ is **extreme** if
every ray $r'$ with $Z(r) \subseteq Z(r')$ satisfies $r' \simeq r$. The extreme rays are, up to
positive scaling, the unique minimal generating set of $P(A)$: every point of $P(A)$ is a
nonnegative combination of them.

**Lemma (irreversible networks).** If every reaction is irreversible, the EMs are exactly the
extreme rays of $P = \{ v \in \mathbb{R}^q : N v = 0,\ v \ge 0 \}$.

**Theorem (splitting reversible reactions).** Let $S'$ be the network obtained from $S$ by replacing
each reversible reaction $i$ by a forward reaction $(i, +1)$ and a backward reaction $(i, -1)$, so its
stoichiometric matrix is $N' = [\, N \ \ -N_{\mathrm{Rev}} \,]$. Then the set of EMs of $S'$ is the
union of

1. the reconfigured EMs of $S$ (a flux $v_i$ of a reversible reaction becomes
   $v'_{(i,+1)} = \max(v_i, 0)$, $v'_{(i,-1)} = \max(-v_i, 0)$), and
2. the futile two-cycles formed by the forward and backward copies of one reversible reaction.

Hence the EMs of any network are obtained, after discarding the two-cycles and mapping back, from
the extreme rays of the pointed cone
$\{ v' \in \mathbb{R}^{q + |\mathrm{Rev}|} : N' v' = 0,\ v' \ge 0 \}$.

## Expansion

For the lemma, write $P$ as $\{ v : A v \ge 0 \}$ with $A = [\, N^{T}\ \ -N^{T}\ \ I \,]^{T}$; the
identity block makes $A$ full rank, so $P$ is pointed. The $2m$ rows coming from $\pm N$ are active
at every point of $P$, so comparing zero sets reduces to comparing the zero patterns of the $q$ sign
constraints, that is, to reverse inclusion of supports. The extreme-ray condition
"$Z(e) \subseteq Z(e') \Rightarrow e' \simeq e$" is then literally "$R(e') \subseteq R(e)
\Rightarrow e' \simeq e$", the definition of an EM.

With reversible reactions, $P$ contains a lineality space and has no unique extreme-ray
generating set. Splitting each reversible reaction is the same device that brings a linear program
to canonical form ($v = v^{+} - v^{-}$ with $v^{\pm} \ge 0$); it makes the cone pointed, and the
theorem shows the only new support-minimal vectors are the trivial cycles $v'_{(i,+1)} =
v'_{(i,-1)} > 0$. Consequently any extreme-ray enumeration algorithm, such as the double
description method, computes EMs: the classical tableau algorithm and the null-space algorithm are
two initializations of it.

## Sources

- J. Gagneur, S. Klamt, "Computation of elementary modes: a unifying framework and the new binary
  approach", BMC Bioinformatics 5 (2004) 175, Results, Lemma 1 and Theorem 1 (proof in Methods),
  <https://doi.org/10.1186/1471-2105-5-175> (PMC544875).
