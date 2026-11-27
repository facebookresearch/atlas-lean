# Büchi acceptance for lossy counter machines is Σ⁰₁-complete

Whether a lossy counter machine has a run from a given configuration that visits a given location infinitely often is $\Sigma^0_1$-complete, and so is the equivalent question whether it has a reachable loop through that location; for reliable Minsky machines the Büchi problem is $\Sigma^1_1$-complete.

**Problems (Schnoebelen).** For a lossy counter machine $M$, a configuration $\sigma_0$ and a location $\ell$:

- *Büchi:* is there a run starting from $\sigma_0$ that visits $\ell$ infinitely many times?
- *Looping on location:* is there a looping run on $\ell$, that is, $\sigma_0 \to^\ast \langle \ell, \vec{a} \rangle \to^+ \langle \ell, \vec{a} \rangle$ for some counter values $\vec{a}$?

**Theorem (Schnoebelen).** Büchi and looping on location are $\Sigma^0_1$-complete for lossy counter machines.

The two problems coincide: by Dickson's lemma an infinite run visiting $\ell$ infinitely often passes through $\langle \ell, \vec{a}_i \rangle$ and later $\langle \ell, \vec{a}_j \rangle$ with $\vec{a}_i \le \vec{a}_j$, and monotonicity of lossy steps turns this into a loop on $\ell$. A loop is a finite witness, which gives membership in $\Sigma^0_1$; unlike termination, the absence of Büchi runs has no finite witness, so Büchi is not decidable.

## Depends on

- [Lossy counter machines](lossy-counter-machines.md)
- [Σ_n sets](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For hardness, take a Minsky machine $M$ with a start location $\ell_{\mathrm{init}}$ and an accepting location $\ell_{\mathrm{end}}$, and put it on a budget: an extra counter $B$ balances every increment and decrement, so the total of the counters is constant along reliable runs and lossy runs cannot increase it. The new machine $M'$ first loops at a location $\ell_0$ to give $B$ any value, then moves to $\ell_1$ and runs the budgeted machine from $\ell_{\mathrm{init}}$; from $\ell_{\mathrm{end}}$ it moves the total of all counters back into $B$, resets the others to $0$ and returns to $\ell_1$. Then $M$ has an accepting run from $\langle \ell_{\mathrm{init}}, \vec{0} \rangle$ if and only if $M'$ has a lossy run from $\langle \ell_0, \vec{0} \rangle$ visiting $\ell_1$ infinitely often: such a run cannot increase the total after leaving $\ell_0$, so eventually it makes only reliable steps, which simulate an accepting run of $M$. Existence of an accepting run of a Minsky machine is $\Sigma^0_1$-complete.

## Sources

- Philippe Schnoebelen, "Lossy Counter Machines Decidability Cheat Sheet", Reachability Problems (RP 2010), Lecture Notes in Computer Science, pp. 51–75, 2010, <https://doi.org/10.1007/978-3-642-15349-5_4>; Section 5 (problem definitions, Lemma 5.1 and Theorem 5.2) and Section 7.3 (Proposition 7.3 and Corollary 7.4), read in the open-access copy at <http://www.lsv.fr/Publis/PAPERS/PDF/phs-rp10.pdf>.
