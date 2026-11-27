# The global calculus of choreographies

The global calculus describes a system of communicating participants as one choreography of session initiations, in-session communications and labeled choices.

**Choreographies.** With participants $A, B, \dots$, shared (service) channels $a, b$, session channels $k$, variables $x, y$, process variables $X$, branching labels $l_i$ and expressions $e$ (evaluated at a participant: $e@A$ uses the variables located at $A$), choreographies are

$$
C ::= \mathbf 0 \mid A \to B : a(k).\,C \mid A \to B : k\langle e, y \rangle.\,C \mid A \to B : k[\{l_i : C_i\}_{i \in I}] \mid C_1 \mid C_2 \mid \mathbf{if}\ e@A\ \mathbf{then}\ C_1\ \mathbf{else}\ C_2 \mid X \mid \mu X.\,C,
$$

for inaction, session initiation by $A$ on $B$'s service channel $a$ with a fresh session channel $k$ bound in $C$, communication of the value of $e$ at $A$ into the variable $y$ at $B$, labeled choice, parallel composition, conditional and recursion. Structural congruence $\equiv$ makes $\mid$ a commutative monoid with unit $\mathbf 0$, includes α-conversion and unfolds $\mu X.\,C \equiv C[\mu X.\,C / X]$.

**Semantics.** A configuration $(\sigma, C)$ pairs a state $\sigma$, mapping located variables $x@A$ to values, with a choreography. Labelled transitions $(\sigma, C) \xrightarrow{\ell} (\sigma', C')$, with labels $\ell$ for initiation ($A \to B : a(h)$, $h$ fresh), communication ($A \to B : k$) and branch selection ($A \to B : k[l_i]$), are given by the expected rules: a communication evaluates $e$ in $A$'s part of $\sigma$ and updates $y@B$; a conditional evaluates its guard and proceeds in the chosen branch; parallel composition interleaves; transitions are closed under $\equiv$.


## Depends on

None.

## Proof depends on

None.

## Expansion

The calculus is a monadic version of the global calculus of Carbone, Honda and Yoshida, in which selection and value passing are separate actions. The expression language is left unspecified, with a decidable equality; the undecidability proof uses string values with concatenation.

## Sources

- Marco Carbone, Davide Grohmann, Thomas T. Hildebrandt and Hugo A. López, "A Logic for Choreographies", in *Proceedings of the 3rd Workshop on Programming Language Approaches to Concurrency and Communication-cEntric Software (PLACES 2010)*, Electronic Proceedings in Theoretical Computer Science 69, 2011, pp. 29–43, <https://doi.org/10.4204/EPTCS.69.3>; read in arXiv:1110.4159v1, <https://arxiv.org/abs/1110.4159v1>: Definition 2.1 and Sections 2.1–2.2 (the global calculus: syntax, structural congruence and operational semantics), in the numbering of that version.
