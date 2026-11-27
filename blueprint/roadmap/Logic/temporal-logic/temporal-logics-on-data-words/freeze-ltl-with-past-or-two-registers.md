# Freeze LTL with past or a second register is Σ¹₁-complete on data words

Satisfiability of linear temporal logic with the freeze quantifier over data words is Σ⁰₁-complete over finite words and Σ¹₁-complete over infinite words as soon as one register is combined with a past operator, or two registers are used with future operators only.

**Setting.** A *data word* over a finite alphabet $\Sigma$ is a finite or infinite sequence of pairs of a letter of $\Sigma$ and a datum from an infinite set, where data can only be compared for equality. *LTL with the freeze quantifier*, $\mathrm{LTL}^{\downarrow}(\mathcal O)$, extends [LTL](../linear-temporal-logic/formula.md) over the letters, with temporal operators from a set $\mathcal O$ among next $\mathsf X$, previous $\mathsf X^{-1}$, until $\mathsf U$, since $\mathsf S$, eventually $\mathsf F$ and sometime-in-the-past $\mathsf F^{-1}$, by registers $r$: ${\downarrow_r}\varphi$ stores the datum at the current position in $r$ and evaluates $\varphi$, and ${\uparrow_r}$ holds when the current datum equals the one stored in $r$. $\mathrm{LTL}^{\downarrow}_n(\mathcal O)$ allows $n$ registers. *Satisfiability* asks whether a sentence holds at the first position of some finite, respectively infinite, data word.

**Theorem (Demri and Lazić).**

1. Over finite data words, satisfiability of $\mathrm{LTL}^{\downarrow}_1(\mathsf X,\mathsf F,\mathsf F^{-1})$ and of $\mathrm{LTL}^{\downarrow}_2(\mathsf X,\mathsf F)$ is $\Sigma^0_1$-complete (Theorems 4.2 and 5.4).
2. Over infinite data words, satisfiability of the same two fragments is $\Sigma^1_1$-complete (Theorems 4.2 and 5.4).

The upper bounds hold for the full logic $\mathrm{LTL}^{\downarrow}(\mathsf X,\mathsf X^{-1},\mathsf U,\mathsf S)$ with any number of registers. By contrast, satisfiability of the future fragment $\mathrm{LTL}^{\downarrow}_1(\mathsf X,\mathsf U)$ with one register is decidable over finite data words, though not primitive recursive already for $\mathrm{LTL}^{\downarrow}_1(\mathsf X,\mathsf F)$, and over infinite data words it is $\Pi^0_1$-complete (Theorems 4.4 and 5.2). The same bounds hold for nonemptiness of the corresponding classes of alternating register automata.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The lower bounds reduce nonemptiness of Minsky counter automata, which is $\Sigma^0_1$-complete over finite words and $\Sigma^1_1$-complete over infinite words (Theorem 2.9(a)): a run is coded as a data word in which data pair each decrement of a counter with an earlier increment of it. With future operators and one register the encoding can only be enforced up to incrementing errors, which is why that fragment stays decidable over finite words; the past operator $\mathsf F^{-1}$, or a second register, lets the formula check that each decrement is matched by an earlier increment, which excludes the errors. The upper bounds come from translating formulas into two-way alternating register automata, whose accepting runs are described arithmetically over finite words and by a second-order existential statement over infinite words.

## Sources

- S. Demri and R. Lazić, "LTL with the freeze quantifier and register automata", *ACM Transactions on Computational Logic* 10(3), article 16, pp. 1–30, 2009, doi:[10.1145/1507244.1507246](https://doi.org/10.1145/1507244.1507246); read in arXiv:cs/0610027v3 ([arXiv](https://arxiv.org/abs/cs/0610027v3)), whose numbering is used: data words and $\mathrm{LTL}^{\downarrow}$ in Section 2, Theorem 2.9 on counter automata, Theorems 4.1, 4.2 and 4.4, and Theorems 5.2 and 5.4 with their proofs. A conference version appeared in *21st Annual IEEE Symposium on Logic in Computer Science (LICS 2006)*, pp. 17–26, doi:[10.1109/LICS.2006.31](https://doi.org/10.1109/LICS.2006.31).
