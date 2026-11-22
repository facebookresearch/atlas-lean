# Formalized Löb theorem

In a Hilbert–Bernays–Löb provability structure, suppose that for every sentence $A$ there is a
sentence $B$ with $T \vdash B \to (\mathrm{Prov}(B) \to A)$ and $T \vdash (\mathrm{Prov}(B) \to A) \to B$
(the diagonal lemma for $\mathrm{Prov}(x) \to A$). Then for every $A$,

$$T \vdash \mathrm{Prov}(\mathrm{Prov}(A) \to A) \to \mathrm{Prov}(A).$$

Proof: the modal formula
$\Box(q \to (\Box q \to p)) \to \Box((\Box q \to p) \to q) \to \Box(\Box p \to p) \to \Box p$ is valid on
transitive models, hence a K4 theorem. Realize it with $p \mapsto A$, $q \mapsto B$, and discharge
the first two hypotheses by D1 applied to the two halves of the fixed-point equation.

## Informally uses

- [Realizations of K4 theorems are theorems](thm-realize-k4.md)
- [K4-theorems are the formulas valid in every transitive Kripke model](../soundness-and-completeness-of-normal-modal-logic/derivable-k4-iff.md)

## Sources

- M. H. Löb, "Solution of a problem of Leon Henkin", *Journal of Symbolic Logic* 20 (1955),
  115–118.
- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §1 and §4.1.
