# Expansion-based QBF calculi: universal expansion resolution and IR-calc

Expansion-based QBF calculi work on existential literals annotated with partial assignments to universal variables: universal expansion resolution instantiates every universal variable in axioms and then resolves, while IR-calc allows partial annotations and instantiation.

Let $\Phi = Q_1 X_1 \dots Q_k X_k .\, \phi$ be a prenex QBF with CNF matrix. An **annotated literal** $l^\sigma$ is an existential literal $l$ with an assignment $\sigma$ to universal variables of level smaller than $\mathrm{lv}(l)$; for an assignment $\tau$ write $l^{[\tau]}$ for $l$ annotated with the part of $\tau$ on universal variables quantified before $l$.

**Universal expansion resolution** ($\forall\mathsf{Exp\text{+}Res}$) has two rules:

- **axiom:** for a clause $C \in \phi$ and a complete assignment $\tau$ to the universal variables, derive $\{l^{[\tau]} : l \in C \text{ existential}\} \cup \{\tau(l) : l \in C \text{ universal}\}$, keeping only the clauses in which no universal literal is made true;
- **resolution:** from $C_1 \lor x^\tau$ and $C_2 \lor \overline{x}^\tau$ derive $C_1 \lor C_2$.

**IR-calc** generalizes this: its axiom uses the assignment $\tau = \{0/u : u \text{ universal in } C\}$ falsifying the universal literals of $C$ (with $0/\overline{x}$ meaning $1/x$), so annotations may be partial; it has the resolution rule on identically annotated literals, and an **instantiation** rule deriving $\mathrm{inst}(\tau, C) = \{l^{[\sigma \curlyvee \tau]} : l^\sigma \in C\}$ for an assignment $\tau$ to universal variables with range $\{0,1\}$, where the **completion** $\sigma \curlyvee \tau$ takes values from $\sigma$ where defined and from $\tau$ elsewhere. **IRM-calc** adds merging of annotations into the symbol $*$. A refutation derives the empty clause.

## Expansion

These systems model expansion-based QBF solving, which expands universal quantifiers into copies of existential variables. IR-calc p-simulates both $\forall\mathsf{Exp\text{+}Res}$ and Q-resolution, and IRM-calc p-simulates IR-calc and long-distance Q-resolution. In the other direction, expansion-based and CDCL-based systems are incomparable: parity formulas are easy for $\forall\mathsf{Exp\text{+}Res}$ but hard for QU-resolution, while the formulas of Kleine Büning, Karpinski and Flögel are easy for long-distance and universal resolution but hard for IR-calc.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, L. Chew, M. Janota, "Proof complexity of resolution-based QBF calculi", *STACS 2015*, LIPIcs 30, 76-89, doi:10.4230/LIPIcs.STACS.2015.76 (Section 2, Figures 3, 4 and 5 with the rules of universal expansion resolution, IR-calc and IRM-calc, and the stated simulations).
