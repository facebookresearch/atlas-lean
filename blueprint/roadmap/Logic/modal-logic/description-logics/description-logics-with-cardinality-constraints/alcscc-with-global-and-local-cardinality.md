# The description logic ALCSCC++ with global and local cardinality constraints

$\mathcal{ALCSCC}^{++}$ extends the description logic $\mathcal{ALC}$ with constraint expressions in quantifier-free Boolean algebra with Presburger arithmetic, which may mix the role successors of an element (local) with whole concept extensions (global); $\mathcal{ALCISCC}^{++}$ also allows inverse roles. Interpretations are finite.

**QFBAPA.** Set terms are built from set variables and the constants $\emptyset$, $\mathcal{U}$ with $\cap$, $\cup$ and complement. Set constraints are $s = t$ and $s \subseteq t$; Presburger expressions are built from integer constants and cardinalities $|s|$ by addition and multiplication by integer constants; cardinality constraints are $k = \ell$, $k < \ell$ and $N \mid \ell$ with $N$ an integer constant. QFBAPA formulas are Boolean combinations of set and cardinality constraints, evaluated under substitutions assigning finite sets.

**Concepts.** Over finite sets $N_C$ of concept names and $N_R$ of role names, concepts are concept names, $C \sqcap D$, $C \sqcup D$, $\neg C$, and *constraint expressions* $\mathrm{sat}(\mathit{con})$, where $\mathit{con}$ is a set or cardinality constraint using role names and already defined concepts as set variables. In $\mathcal{ALCISCC}^{++}$, inverse roles $r^-$ may occur wherever role names may, with $(r^-)^{\mathcal{I}} = \{(e,d) : (d,e) \in r^{\mathcal{I}}\}$.

**Semantics.** A finite interpretation $\mathcal{I}$ has a finite nonempty domain $\Delta^{\mathcal{I}}$, with $A^{\mathcal{I}} \subseteq \Delta^{\mathcal{I}}$ and $r^{\mathcal{I}} \subseteq \Delta^{\mathcal{I}} \times \Delta^{\mathcal{I}}$. For $d \in \Delta^{\mathcal{I}}$ the substitution $\sigma_d$ maps $\mathcal{U}$ to $\Delta^{\mathcal{I}}$, each concept $C$ to $C^{\mathcal{I}}$ (globally) and each role $r$ to the successor set $r^{\mathcal{I}}(d) = \{e : (d,e) \in r^{\mathcal{I}}\}$ (locally). Booleans are interpreted as usual and $\mathrm{sat}(\mathit{con})^{\mathcal{I}} = \{d : \sigma_d \text{ satisfies } \mathit{con}\}$. A concept $C$ is *satisfiable* if $C^{\mathcal{I}} \neq \emptyset$ for some finite $\mathcal{I}$.

**Queries.** A Boolean conjunctive query (CQ) is a finite set of atoms $r(x,y)$ and $C(z)$ over variables; $\mathcal{I} \models q$ if some map of the variables into $\Delta^{\mathcal{I}}$ satisfies every atom. A knowledge base *finitely entails* $q$ if every finite model of it satisfies $q$; since $\mathcal{ALCSCC}^{++}$ has only finite interpretations, its entailment is finite entailment.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

None.

## Expansion

Global cardinality constraints such as $|A| = |B|$ and local ones such as "an element has as many $r$-successors as $s$-successors" are both expressible, and $\mathcal{ALCSCC}^{++}$ concepts can express $\mathcal{ALC}$ ECBoxes and $\mathcal{ALCSCC}$ TBoxes (Proposition 4). Concept satisfiability in $\mathcal{ALCSCC}^{++}$ is NEXPTIME-complete, and conjunctive query entailment is decidable for the weaker logic $\mathcal{ALCSCC}$, whose constraints are local only.

## Sources

- Franz Baader, Bartosz Bednarczyk and Sebastian Rudolph, "Satisfiability and query answering in description logics with global and local cardinality constraints", in *ECAI 2020: 24th European Conference on Artificial Intelligence*, Frontiers in Artificial Intelligence and Applications 325, IOS Press, 2020, doi:10.3233/FAIA200146; read as arXiv:2002.06072v1, <https://arxiv.org/abs/2002.06072v1>: Section 2 (QFBAPA and the definition of $\mathcal{ALCSCC}^{++}$), Section 5 (inverse roles) and Section 6 (conjunctive queries and finite entailment), with Proposition 4, Theorem 8 and the abstract, of arXiv:2002.06072v1.
