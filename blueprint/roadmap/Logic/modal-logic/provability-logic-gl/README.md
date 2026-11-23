# Provability logic GL

The provability logic GL (Gödel–Löb logic) is the normal modal logic obtained from K by adding
Löb's axiom $\Box(\Box p \to p) \to \Box p$. Reading $\Box$ as "is provable in Peano arithmetic",
GL is exactly the propositional modal logic of the provability predicate: every theorem of GL is
arithmetically valid (soundness, which needs only the Hilbert–Bernays–Löb derivability conditions
and the diagonal lemma), and conversely every modal formula all of whose arithmetical realizations
are provable in PA is a theorem of GL (Solovay's arithmetical completeness theorem, 1976).

The development follows the order in which the subject is usually taught.

1. **Axioms and first theorems.** GL proves axiom 4, so it contains K4; it proves the modal form of
   Gödel's second incompleteness theorem, $\neg\Box\bot \to \neg\Box\neg\Box\bot$; it is consistent,
   does not prove reflection $\Box\bot \to \bot$, and strictly extends K4.
2. **Kripke semantics.** Löb's axiom, hence every theorem of GL, is valid on every transitive,
   conversely well-founded frame, in particular on every finite strict partial order. Conversely,
   GL is complete for finite strict partial orders (Segerberg 1971), and Löb's axiom holds on a
   frame exactly when the frame is transitive and conversely well-founded.
3. **Fixed points.** Self-reference is eliminable: if $p$ occurs in $A(p)$ only under boxes, $A$
   has a fixed point $H$ without $p$, with $\mathrm{GL} \vdash H \leftrightarrow A(H)$ (de Jongh and
   Sambin, 1975), and it is unique up to provable equivalence. For a single boxed
   occurrence, $A(p) = B(\Box C(p))$, the fixed point is $B(\Box C(B(\top)))$. The fixed point of $\neg\Box p$ is the
   consistency statement $\neg\Box\bot$, the modal shadow of the Gödel sentence.
4. **Arithmetic.** In an abstract theory with the derivability conditions D1–D3 and diagonal fixed
   points for the formulas $\mathrm{Prov}(x) \to A$, the formalized Löb theorem, Löb's theorem and
   the arithmetical soundness of GL are proved by realizing K4 theorems.

**Solovay's arithmetical completeness theorem** (R. M. Solovay, "Provability interpretations of
modal logic", *Israel Journal of Mathematics* 25 (1976), 287–304) needs an arithmetization of Peano arithmetic with a provability predicate on its sentences, which
the abstract provability structures below do not provide. It states that for every modal formula $\varphi$, $\mathrm{GL} \vdash \varphi$ if and only if
$\mathrm{PA} \vdash f(\varphi)$ for every realization $f$, where $f$ sends atoms to arithmetical
sentences, commutes with the connectives and sends $\Box\psi$ to $\mathrm{Prov}_{\mathrm{PA}}(\ulcorner
f(\psi) \urcorner)$. The direction from left to right is arithmetical soundness; the converse is
proved by simulating a finite Kripke countermodel (from Segerberg's theorem) inside PA by a
self-referential "Solovay function". It holds more generally for every $\Sigma_1$-sound theory
extending $\mathrm{I}\Delta_0 + \mathrm{EXP}$ with a natural provability predicate (de Jongh et
al., 1991), as reported in R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §4.2 and §5.1. Solovay's paper also characterizes
the sentences true in the standard model by the logic GLS.

## Axioms and first theorems

- [Löb's axiom](axiom-lob.md)
- [Extra axioms of the provability logic GL](gl.md)
- [Modus ponens with a K theorem](mp-of-k.md)
- [GL proves axiom 4](axiom-four-gl.md)
- [Every theorem of K4 is a theorem of GL](gl-of-k4.md)
- [Modus ponens with a K4 theorem in GL](mp-of-k4.md)
- [Modal Gödel's second incompleteness theorem](godel-second-gl.md)
- [The Gödel sentence of GL](godel-sentence-gl.md)
- [The one-world irreflexive Kripke model](irreflexive-point.md)
- [GL does not prove reflection for `⊥`](not-derivable-axiom-t-bot-gl.md)
- [Consistency of GL](not-derivable-bot-gl.md)
- [K4 does not prove Löb's axiom](not-derivable-axiom-lob-k4.md)

## Kripke semantics

- [Löb's axiom is valid on transitive conversely well-founded frames](valid-axiom-lob.md)
- [Soundness of GL](valid-gl.md)
- [Soundness of GL for finite strict partial orders](valid-gl-of-finite.md)
- [Completeness of GL for finite strict partial orders](derivable-gl-iff-finite.md)
- [Frame correspondence for Löb's axiom](frame-valid-axiom-lob-iff.md)

## Fixed points

- [Atom occurring only under a box](modalised.md)
- [A modalised atom is read only at visible worlds](satisfies-update-atom-congr-of-modalised.md)
- [Uniqueness of fixed points in GL](fixed-point-unique-gl.md)
- [The de Jongh–Sambin fixed point for one boxed occurrence](fixed-point-gl-of-box.md)
- [The de Jongh–Sambin fixed point theorem](fixed-point-gl.md)

## Arithmetical interpretation

- [Hilbert–Bernays–Löb provability structure](hilbert-bernays-lob-structure.md)
- [Arithmetical realization of a modal formula](realize.md)
- [Realizations of theorems of a normal modal logic are theorems](thm-realize.md)
- [Realizations of K4 theorems are theorems](thm-realize-k4.md)
- [Formalized Löb theorem](formalized-lob.md)
- [Löb's theorem](lob-theorem.md)
- [Arithmetical soundness of GL](thm-realize-gl.md)

## Related topics

- [Normal modal logics](../normal-modal-logics/README.md): the Hilbert systems $\mathrm{K} \oplus \Lambda$
  of which GL is an instance.
- [Soundness and completeness of normal modal logics](../soundness-and-completeness-of-normal-modal-logic/README.md):
  K4 and its completeness, used for every GL derivation here.
- [Kripke semantics](../kripke-semantics/README.md): substitution and locality of truth.
