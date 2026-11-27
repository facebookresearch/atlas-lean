# The global calculus and its global logic

The global calculus describes a system of communicating participants as one choreography of session initiations, in-session communications and labeled choices; the global logic adds action modalities, an eventually operator and a spatial conjunction for reasoning about choreographies in a given state.

**Choreographies.** With participants $A, B, \dots$, shared (service) channels $a, b$, session channels $k$, variables $x, y$, process variables $X$, branching labels $l_i$ and expressions $e$ (evaluated at a participant: $e@A$ uses the variables located at $A$), choreographies are

$$
C ::= \mathbf 0 \mid A \to B : a(k).\,C \mid A \to B : k\langle e, y \rangle.\,C \mid A \to B : k[\{l_i : C_i\}_{i \in I}] \mid C_1 \mid C_2 \mid \mathbf{if}\ e@A\ \mathbf{then}\ C_1\ \mathbf{else}\ C_2 \mid X \mid \mu X.\,C,
$$

for inaction, session initiation by $A$ on $B$'s service channel $a$ with a fresh session channel $k$ bound in $C$, communication of the value of $e$ at $A$ into the variable $y$ at $B$, labeled choice, parallel composition, conditional and recursion. Structural congruence $\equiv$ makes $\mid$ a commutative monoid with unit $\mathbf 0$, includes α-conversion and unfolds $\mu X.\,C \equiv C[\mu X.\,C / X]$.

**Semantics.** A configuration $(\sigma, C)$ pairs a state $\sigma$, mapping located variables $x@A$ to values, with a choreography. Labelled transitions $(\sigma, C) \xrightarrow{\ell} (\sigma', C')$, with labels $\ell$ for initiation ($A \to B : a(h)$, $h$ fresh), communication ($A \to B : k$) and branch selection ($A \to B : k[l_i]$), are given by the expected rules: a communication evaluates $e$ in $A$'s part of $\sigma$ and updates $y@B$; a conditional evaluates its guard and proceeds in the chosen branch; parallel composition interleaves; transitions are closed under $\equiv$.

**Global logic.** Formulas are

$$
\phi ::= \exists x.\,\phi \mid \phi \land \phi \mid \neg \phi \mid \langle \ell \rangle \phi \mid \mathsf{end} \mid e_1@A = e_2@B \mid \phi \mid \phi \mid \Diamond \phi,
$$

where $\exists$ ranges over channels, participants, labels and expression placeholders. Satisfaction $C \models_\sigma \phi$: $\mathsf{end}$ is true if $C \equiv \mathbf 0$; $e_1@A = e_2@B$ if both evaluate in $\sigma$ to the same value; $\langle \ell \rangle \phi$ if $(\sigma, C) \xrightarrow{\ell} (\sigma', C')$ with $C' \models_{\sigma'} \phi$; $\Diamond \phi$ if $(\sigma, C) \to^* (\sigma', C')$ with $C' \models_{\sigma'} \phi$; $\phi \mid \chi$ if $C \equiv C_1 \mid C_2$ with $C_1 \models_\sigma \phi$ and $C_2 \models_\sigma \chi$; the Boolean connectives and $\exists$ (for some value of the appropriate sort) as usual.

## Depends on

None.

## Proof depends on

None.

## Expansion

The calculus is a monadic version of the global calculus of Carbone, Honda and Yoshida, in which selection and value passing are separate actions. The logic extends Hennessy–Milner logic with first-order quantification, the eventually operator of temporal logic and a spatial composition operator in the style of separation and spatial logics; always, next and box modalities are derived. The expression language is left unspecified, with a decidable equality; the undecidability proof uses string values with concatenation.

## Sources

- Marco Carbone, Davide Grohmann, Thomas T. Hildebrandt and Hugo A. López, "A Logic for Choreographies", in *Proceedings of the 3rd Workshop on Programming Language Approaches to Concurrency and Communication-cEntric Software (PLACES 2010)*, Electronic Proceedings in Theoretical Computer Science 69, 2011, pp. 29–43, <https://doi.org/10.4204/EPTCS.69.3>; arXiv:1110.4159v1, <https://arxiv.org/abs/1110.4159v1>: Section 2 (the global calculus: syntax, structural congruence and operational semantics) and Section 3 (syntax and satisfaction of the global logic).
