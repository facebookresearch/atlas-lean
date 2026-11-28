# Modal free description logics with non-rigid designators

Modal free description logics extend the description logic $\mathcal{ALCO}_u$ (with nominals and the universal role) by modal diamonds $\Diamond_i$ and allow individual names that may designate different objects, or nothing, in different worlds. Their models are Kripke frames whose worlds carry partial description logic interpretations, with constant or expanding domains.

**Syntax.** Fix countably infinite disjoint sets of concept names $A$, role names $r$ and individual names $a$, and modalities $I = \{1, \dots, n\}$. Concepts of $\mathcal{ML}^n_{\mathcal{ALCO}_u}$ are

$$
C ::= A \mid \{a\} \mid \neg C \mid C \sqcap C \mid \exists r.C \mid \exists u.C \mid \Diamond_i C,
$$

where $u$ is the universal role and $i \in I$; $\Box_i C = \neg\Diamond_i\neg C$, and $\sqcup$, $\forall$, $\Rightarrow$ are the usual abbreviations. (The full language also has definite descriptions $\iota C$ as terms.) A *concept inclusion* is $C \sqsubseteq D$, and an *ontology* is a finite set of concept inclusions.

**Interpretations.** A frame is $\mathfrak{F} = (W, \{R_i\}_{i \in I})$. An interpretation with *constant domains* based on $\mathfrak{F}$ is $\mathfrak{M} = (\mathfrak{F}, \Delta, \mathcal{I})$ with one nonempty domain $\Delta$ and, for each world $w$, a partial description logic interpretation $\mathcal{I}_w$ mapping each concept name to a subset of $\Delta$, each role name to a binary relation on $\Delta$, $u$ to $\Delta \times \Delta$, and each individual name in *some subset* of the individual names to an element of $\Delta$ (a name *designates* at $w$ if it is mapped). With *expanding domains*, each world has its own domain $\Delta^w$ and $\Delta^w \subseteq \Delta^v$ whenever $w R_i v$. Extensions are defined by $(\neg C)^{\mathcal{I}_w} = \Delta^w \setminus C^{\mathcal{I}_w}$, intersection for $\sqcap$, $(\exists r.C)^{\mathcal{I}_w} = \{d : \exists e \in C^{\mathcal{I}_w},\ (d, e) \in r^{\mathcal{I}_w}\}$, $(\Diamond_i C)^{\mathcal{I}_w} = \{d \in \Delta^w : \exists v\ (w R_i v \wedge d \in C^{\mathcal{I}_v})\}$, and $\{a\}^{\mathcal{I}_w} = \{a^{\mathcal{I}_w}\}$ if $a$ designates at $w$ and $\varnothing$ otherwise.

**Logics and reasoning.** For a class of frames, such as all frames ($\mathsf{K}^n$) or frames whose relations are equivalence relations ($\mathsf{S5}^n$), $\mathsf{K}^n_{\mathcal{ALCO}_u}$ and $\mathsf{S5}^n_{\mathcal{ALCO}_u}$ denote the language interpreted over interpretations based on frames of that class. An ontology $\mathcal{O}$ is satisfied in $\mathfrak{M}$ if $C^{\mathcal{I}_w} \subseteq D^{\mathcal{I}_w}$ for all $C \sqsubseteq D$ in $\mathcal{O}$ and all worlds $w$. *Concept satisfiability under global ontology* asks, given $C$ and $\mathcal{O}$, whether some interpretation satisfies $\mathcal{O}$ and has $C^{\mathcal{I}_w} \neq \varnothing$ for some world $w$.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

Non-rigid names model descriptions such as "the general chair of the conference", which can refer to different people in different states or to no one. Concept satisfiability for these logics is linked to satisfiability of the one-variable fragment of first-order modal logic with counting; the source proves it NEXPTIME-complete for $\mathsf{S5}^n$ and neighboring logics.

## Sources

- A. Artale, R. Kontchakov, A. Mazzullo and F. Wolter, "Non-rigid designators in modal and temporal free description logics", in *Proceedings of the 21st International Conference on Principles of Knowledge Representation and Reasoning (KR 2024)*, 2024, pp. 82–93, doi:10.24963/kr.2024/8; read as arXiv:2405.07656v2 (extended version), <https://arxiv.org/abs/2405.07656v2>: the section "Preliminaries" (syntax, partial interpretations with constant and expanding domains, extensions of concepts, ontologies and concept satisfiability).
