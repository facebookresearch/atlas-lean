# Abstract DPLL with learning

Let $F$ be a propositional formula in conjunctive normal form, viewed as a set of clauses. A *state* is either FailState or a pair $M \parallel F$ of a clause set $F$ and a sequence $M$ of literals in which each literal is annotated as a decision literal $l^d$ or not. $M$ is read as a partial assignment, and $M \models \neg C$ means that every literal of the clause $C$ is false in $M$. The *Basic DPLL system* $\mathcal{B}$ has four transition rules:

- **UnitPropagate:** $M \parallel F, C \vee l \Longrightarrow M\, l \parallel F, C \vee l$ if $M \models \neg C$ and $l$ is undefined in $M$.
- **Decide:** $M \parallel F \Longrightarrow M\, l^d \parallel F$ if $l$ or $\neg l$ occurs in a clause of $F$ and $l$ is undefined in $M$.
- **Fail:** $M \parallel F, C \Longrightarrow \mathrm{FailState}$ if $M \models \neg C$ and $M$ contains no decision literal.
- **Backjump:** $M\, l^d\, N \parallel F, C \Longrightarrow M\, l' \parallel F, C$ if $M\, l^d\, N \models \neg C$, and some *backjump clause* $C' \vee l'$ satisfies:
    - $F, C \models C' \vee l'$;
    - $M \models \neg C'$;
    - $l'$ is undefined in $M$;
    - $l'$ or $\neg l'$ occurs in $F$ or in $M\, l^d\, N$.

The *DPLL system with learning* $\mathcal{L}$ adds two rules:

- **Learn:** $M \parallel F \Longrightarrow M \parallel F, C$ if every atom of $C$ occurs in $F$ or in $M$, and $F \models C$.
- **Forget:** $M \parallel F, C \Longrightarrow M \parallel F$ if $F \models C$.

The **Restart** rule $M \parallel F \Longrightarrow \emptyset \parallel F$ may be added. A derivation for $F$ starts from $\emptyset \parallel F$. A state is *final with respect to Basic DPLL* if no rule of $\mathcal{B}$ applies to it.

The literals of $M$ after the $i$-th decision literal and before the next one form *decision level* $i$. Learn models conflict-driven clause learning, typically applied to the backjump clause right after Backjump. Forget models lemma deletion, and Restart models solver restarts. Chronological backtracking is the special case of Backjump in which the backjump clause consists of the negations of all decision literals.

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 2: Definition 2.1 (the Classical DPLL rules, decision levels), Definition 2.4 (the Basic DPLL system with Backjump), Definition 2.5 (the DPLL system with learning: Learn and Forget), and Definition 2.14 (the Restart rule).
