# Combinatory sequence-to-shape maps and their large preimages

**Definition.** Fix the abstract alphabet $\mathcal A=\{\mathbf A,\mathbf B,\mathbf C,\mathbf D\}$ and let $Q_4^n$ be the generalized $n$-cube: the graph on sequences $(x_1,\dots,x_n)\in\mathcal A^n$ in which two sequences are adjacent when they differ in exactly one position. A *pairing relation* is $\mathcal R\subset\mathcal A\times\mathcal A$ that is symmetric, irreflexive, and satisfies $(x,y),(y,z)\in\mathcal R,\ x\ne z\Rightarrow(x,z)\notin\mathcal R$; equivalently, $\mathcal R$ is a bipartite graph on $\mathcal A$ (Watson–Crick plus G–U pairs is an example). Given a base graph $H$ on $\{1,\dots,n\}$, the *shape* of $v=(x_1,\dots,x_n)$ is the $H$-subgraph $H_{\mathcal R}(v)$ with vertex set $\{1,\dots,n\}$ and edge set

$$
\{\{i,k\}\in E(H): (x_i,x_k)\in\mathcal R\},
$$

and the *combinatory map* is $\vartheta_H: Q_4^n\to\{H_{\mathcal R}(v)\}$, $v\mapsto H_{\mathcal R}(v)$. A shape is the maximal $H$-subgraph compatible with $\mathcal R$ (a saturated structure). The main case uses $\mathcal R^\dagger$, the path $\mathbf A-\mathbf B-\mathbf D-\mathbf C$ (pairs $\{\mathbf A,\mathbf B\},\{\mathbf D,\mathbf B\},\{\mathbf D,\mathbf C\}$), and the base graph $\mathcal H=C_n(\sigma_n)$, a Hamiltonian cycle $\{\sigma_n(i),\sigma_n(i+1)\}$ for $n$ even, or $C_{n-1}(\sigma_{n-1})$ plus an isolated vertex for $n$ odd.

**Lemma (shapes).** For any $H$: (a) for every relation $\mathcal R$, every shape is bipartite; (b) for $\mathcal R^\dagger$, every induced bipartite subgraph of $H$ is a shape; (c) for $\mathcal R^\dagger$ and $\mathcal H$, every $\mathcal H$-subgraph is a shape.

**Lemma (large preimages).** For $\mathcal R^\dagger$ and $\mathcal H$, with $\mu_\pm=\frac{1\pm\sqrt5}{2}$, there are at least $(\sqrt2)^{\,n-1}$ shapes each having at least

$$
2\big(\mu_+^{\,n}+\mu_-^{\,n}\big)
$$

sequences mapping into it.

## Expansion

Combinatory maps replace the non-crossing constraint of RNA secondary structures by an arbitrary base graph restricting which positions may interact, so a nucleotide may take part in two interactions (as in tertiary contacts, coaxial stacking or base triples). Bipartiteness of shapes follows because an odd cycle of $\mathcal R$-compatible positions would need an odd closed walk in the bipartite graph $\mathcal R$. With the cycle base graph, $\mathcal R^\dagger$ realizes all $2^n$ edge subsets as shapes, comparable to the exponential growth of RNA secondary structures. Counting sequences that realize a fixed cycle-shape is a transfer-matrix problem along the cycle, which is where the Lucas-type quantity $\mu_+^n+\mu_-^n$ appears. As for RNA folding maps, a few shapes have huge preimages and most have tiny ones.

## Sources

- Emma Y. Jin, Jing Qin, Christian M. Reidys. *Neutral Networks of Sequence to Shape Maps* (2007), Sections 2–4: Lemmas 1–2 and Theorems 1–2. <https://doi.org/10.48550/arXiv.0706.0760>
