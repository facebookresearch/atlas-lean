# Query entailment and inseparability between EL and ALC ontologies are undecidable

Deciding whether an EL ontology answers every conjunctive query over a given signature at least as well as an ALC ontology, or whether the two give the same answers, is undecidable, both for knowledge bases and for TBoxes queried with arbitrary data.

**Setting.** A knowledge base (KB) $\mathcal K=(\mathcal T,\mathcal A)$ of a description logic consists of a TBox $\mathcal T$ and an ABox $\mathcal A$ (see [ALC syntax and semantics](../alc-syntax-semantics-and-reasoning-tasks.md)); $\mathcal{EL}$ is the fragment of $\mathcal{ALC}$ with only conjunction, $\top$ and existential restrictions. A *conjunctive query* (CQ) $q(\mathbf x)=\exists\mathbf y\,\varphi(\mathbf x,\mathbf y)$ is a conjunction of concept and role atoms; it is *rooted* (an rCQ) if every variable is connected to an answer variable. For a class $\mathcal Q$ of queries and a signature $\Sigma$ of concept and role names, $\mathcal K_1$ *$\Sigma$-$\mathcal Q$ entails* $\mathcal K_2$ if, for every query in $\mathcal Q$ over $\Sigma$, its certain answers over $\mathcal K_2$ are among its certain answers over $\mathcal K_1$; the two KBs are *$\Sigma$-$\mathcal Q$ inseparable* if each entails the other. For TBoxes and $\Theta=(\Sigma_1,\Sigma_2)$, $\mathcal T_1$ *$\Theta$-$\mathcal Q$ entails* $\mathcal T_2$ if for every ABox $\mathcal A$ over $\Sigma_1$ (consistent with both TBoxes), $(\mathcal T_1,\mathcal A)$ $\Sigma_2$-$\mathcal Q$ entails $(\mathcal T_2,\mathcal A)$, and inseparability is again mutual entailment.

**Theorem (Botoeva, Lutz, Ryzhikov, Wolter and Zakharyaschev).** For $\mathcal Q\in\{\mathrm{CQ},\mathrm{rCQ}\}$:

1. it is undecidable whether an $\mathcal{EL}$ KB $\Sigma$-$\mathcal Q$ entails an $\mathcal{ALC}$ KB, and $\Sigma$-$\mathcal Q$ inseparability between $\mathcal{EL}$ and $\mathcal{ALC}$ KBs is undecidable (Theorems 20–22); both remain undecidable when $\Sigma$ is the full signature (Theorem 24);
2. it is undecidable whether an $\mathcal{EL}$ TBox $\Theta$-$\mathcal Q$ entails an $\mathcal{ALC}$ TBox, and $\Theta$-$\mathcal Q$ inseparability between $\mathcal{EL}$ and $\mathcal{ALC}$ TBoxes is undecidable; for CQs this holds already for full ABox signatures and for $\Theta=(\Sigma_1,\Sigma_2)$ with $\Sigma_1=\Sigma_2$ (Theorem 43).

By contrast, inseparability between $\mathcal{ALC}$ KBs becomes decidable, and 2EXPTIME-complete, when CQs are replaced by unions of CQs or rooted unions of CQs, and CQ inseparability between Horn-$\mathcal{ALC}$ TBoxes is 2EXPTIME-complete. Since $\mathcal{EL}$ is a fragment of Horn-$\mathcal{ALC}$, the theorem also covers entailment of an $\mathcal{ALC}$ ontology by a Horn-$\mathcal{ALC}$ one, the setting of the conference version.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

None.

## Expansion

The proofs reduce the rectangle tiling problem: given tile types with colors, an initial tile type and a border color, is there a tiling of some finite $N\times M$ rectangle with the initial tile in a corner and the border color on the right and top edges? This problem is undecidable. From a tile set one builds an $\mathcal{ALC}$ KB whose models encode grids and an $\mathcal{EL}$ KB such that a CQ over $\Sigma$ separates them exactly when a tiling of some rectangle exists, using the model-theoretic characterization of $\Sigma$-CQ entailment by homomorphisms of materializations into models of the other KB; the inseparability and TBox versions modify these KBs. A good expansion links a page for the undecidability of the rectangle tiling problem; none exists yet.

## Sources

- E. Botoeva, C. Lutz, V. Ryzhikov, F. Wolter and M. Zakharyaschev, "Query inseparability for ALC ontologies", *Artificial Intelligence* 272, pp. 1–51, 2019, doi:[10.1016/j.artint.2018.09.003](https://doi.org/10.1016/j.artint.2018.09.003); read in arXiv:1902.00014v1 ([arXiv](https://arxiv.org/abs/1902.00014v1)), whose numbering is used: the definitions in the introduction and preliminaries, the rectangle tiling problem and Theorems 20, 21, 22 and 24 for KBs, Theorem 43 for TBoxes, and the introduction for the decidable cases.
- E. Botoeva, C. Lutz, V. Ryzhikov, F. Wolter and M. Zakharyaschev, "Query-based entailment and inseparability for ALC ontologies", in *Proceedings of the 25th International Joint Conference on Artificial Intelligence (IJCAI 2016)*, IJCAI/AAAI Press, pp. 1001–1007, 2016; full version arXiv:1604.04164v2 ([arXiv](https://arxiv.org/abs/1604.04164v2)), which states the Horn-$\mathcal{ALC}$ versions; cited beside the journal version read above.
