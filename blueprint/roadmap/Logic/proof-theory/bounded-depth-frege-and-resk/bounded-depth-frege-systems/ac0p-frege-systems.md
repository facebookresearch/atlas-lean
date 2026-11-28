# AC$^0[p]$-Frege systems

For a prime $p$, an AC$^0[p]$-Frege system is a constant-depth sequent calculus over $\neg$, unbounded $\bigvee$ and the counting connectives $MOD_{p,i}$, with axioms fixing the meaning of $MOD_{p,i}$ as "the number of true arguments is congruent to $i$ modulo $p$".

Fix a prime $p$. Formulas are built from variables with $\neg$, unbounded arity $\bigvee$ and unbounded arity connectives $MOD_{p,i}$ for $i=0,\dots,p-1$; the intended meaning of $MOD_{p,i}(y_1,\dots,y_k)$ is $\sum_j y_j\equiv i\pmod p$. Conjunction is not a primitive connective. The *depth* of a formula is the maximal number of alternations of connectives, and the size of a formula or proof is its total number of symbols.

The system $LK(MOD_p)$ is the sequent calculus with the structural rules (weakening, contraction, exchange), the cut rule, the left and right $\neg$ rules, and the unbounded $\bigvee$ rules: from $\varphi_j,\Gamma\longrightarrow\Delta$ for every $j\le t$ infer $\bigvee_{i\le t}\varphi_i,\Gamma\longrightarrow\Delta$, and from $\Gamma\longrightarrow\Delta,\varphi_j$ for some $j\le t$ infer $\Gamma\longrightarrow\Delta,\bigvee_{i\le t}\varphi_i$. There are no rules for $MOD_{p,i}$; instead there are the $\mathbf{MOD}_p$-axioms

$$
MOD_{p,0}(\emptyset),\qquad \neg MOD_{p,i}(\emptyset)\ \ (i=1,\dots,p-1),
$$

$$
MOD_{p,i}(\Gamma,\phi)\equiv\bigl[(MOD_{p,i}(\Gamma)\wedge\neg\phi)\vee(MOD_{p,i-1}(\Gamma)\wedge\phi)\bigr]\quad(i=0,\dots,p-1),
$$

where $i-1$ is taken modulo $p$ and $\Gamma$ is a possibly empty sequence of formulas. The depth-$d$ subsystem $LK_d(MOD_p)$ uses only formulas of depth at most $d$. This system is polynomially equivalent to constant-depth Frege systems with $MOD_{p,i}$ connectives, with only a constant increase in depth under the mutual simulations, because both have the same language.

## Expansion

The circuit analogue is $\mathrm{AC}^0[p]$, for which Razborov and Smolensky proved strong lower bounds (see [Smolensky's theorem](../../../../TheoryOfComputation/circuit-complexity/constant-depth-circuit-lower-bounds/smolensky-s-theorem-mod-q-is-not-in-ac0-p.md)). The source records that adapting the Razborov-Smolensky method to $LK_d(MOD_p)$ had not produced lower bounds: known results concern related systems, such as [bounded-depth Frege with counting axioms](../modular-counting-principles/counting-axioms-modulo-m.md), and Krajíček's paper instead [reduces lower bounds for these systems to a search-tree hardness question](../modular-counting-principles/ac0p-frege-lower-bounds-from-search-trees.md).

## Depends on

- [Bounded-depth Frege proofs](bounded-depth-frege-proofs.md)

## Proof depends on

None.

## Sources

- Jan Krajíček, "A reduction of proof complexity to computational complexity for AC0[p] Frege systems", *Proceedings of the American Mathematical Society* 143, 2015, https://doi.org/10.1090/S0002-9939-2015-12610-X; numbering as in arXiv:1311.2501v4 (Section 1, definition of LK(MOD_p) and LK_d(MOD_p)).
