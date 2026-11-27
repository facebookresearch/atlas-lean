# Model checking context HyperLTL is undecidable

Model checking finite Kripke structures against HyperLTL with context modalities, which let only a chosen subset of the quantified traces advance, is undecidable already with two trace variables and context nesting depth two.

**Theorem (Bozzelli, Peron and Sánchez).** *Context HyperLTL* (HyperLTL$_C$) has the sentences $Q_1 x_1 \cdots Q_n x_n\,\psi$ with trace quantifiers over the traces of a Kripke structure and quantifier-free part

$$
\psi ::= \top \mid p[x] \mid \neg\psi \mid \psi \wedge \psi \mid \mathsf X\psi \mid \psi\,\mathsf U\,\psi \mid \langle C\rangle\psi,
$$

where the context $C$ is a nonempty set of trace variables. A formula is evaluated with a current context: $\mathsf X$ and $\mathsf U$ advance by one, respectively by some number of, positions only the traces bound to variables in the current context, leaving the others in place; $\langle C\rangle\psi$ evaluates $\psi$ with context $C$; at the top level the context is the set of all variables. Let $F_0$ and $F_1$ be the fragments with two trace variables and nesting depth of context modalities $2$ in which, respectively, the quantifier alternation depth is $0$, or it is $1$ and every temporal modality in the scope of a non-global context is $\mathsf F$. Model checking HyperLTL$_C$ is undecidable even for $F_0$ and for $F_1$ (Theorem IV.1 of the source).

The source also identifies a fragment of HyperLTL$_C$ with decidable model checking that is, in a precise sense, maximal.

## Depends on

- [HyperLTL](../hyperltl.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof is a polynomial-time reduction from the halting problem for Minsky two-counter machines. A computation is encoded as a trace of configuration codes, one per transition used, in which the value of each counter is the length of a block of letters after a marker. The constructed sentence asserts two traces bound to $x_1$ and $x_2$ that coincide, that the first is an initial and halting computation code, and, through a quantifier-free formula $\psi_{\mathrm{good}}$ that uses contexts advancing only one of the two copies, that the counter values in consecutive configuration codes are related as the transitions require. The machine halts iff the Kripke structure $K_M$ satisfies the sentence.

## Sources

- L. Bozzelli, A. Peron and C. Sánchez, "Asynchronous Extensions of HyperLTL", in *2021 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, IEEE, 2021, pp. 1–13, <https://doi.org/10.1109/LICS52264.2021.9470583>; numbers from arXiv:2104.12886v1, <https://arxiv.org/abs/2104.12886v1>: Section IV (syntax and semantics of HyperLTL$_C$, the fragments $F_0$ and $F_1$, Theorem IV.1 and its proof).
