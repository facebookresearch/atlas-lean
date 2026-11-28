# Products and commutators of modal logics

The product of Kripke complete modal logics is the logic of all product frames built from their frames, with one accessibility relation acting in each coordinate; the commutator is the least logic containing the components and the commutation and Church–Rosser axioms.

**Product frames.** For unimodal frames $\mathfrak{F}_i = \langle W_i, R_i\rangle$, $i = 1, \dots, n$ with $n \geq 2$, the product $\mathfrak{F}_1 \times \cdots \times \mathfrak{F}_n$ is the $n$-frame $\langle W_1 \times \cdots \times W_n, \bar{R}_1, \dots, \bar{R}_n\rangle$ with $\langle u_1, \dots, u_n\rangle \bar{R}_i \langle v_1, \dots, v_n\rangle$ iff $u_i R_i v_i$ and $u_k = v_k$ for all $k \neq i$.

**Product logics.** $n$-modal formulas, built from a countably infinite set of propositional variables, have boxes $\Box_1, \dots, \Box_n$, interpreted in $n$-frames as usual; $\mathrm{Log}\,\mathcal{C}$ is the set of formulas valid in all frames of a class $\mathcal{C}$, and $\mathrm{Fr}\,L$ the class of frames for a logic $L$. For Kripke complete unimodal logics $L_1, \dots, L_n$, the *product* is

$$
L_1 \times \cdots \times L_n = \mathrm{Log}\{\mathfrak{F}_1 \times \cdots \times \mathfrak{F}_n : \mathfrak{F}_i \in \mathrm{Fr}\,L_i\}.
$$

$\mathbf{K}^n$ is the logic of all $n$-dimensional product frames and $\mathbf{S5}^n$ the logic of products of $n$ equivalence frames.

**Commutators.** With $\Diamond_i = \neg\Box_i\neg$, let $\mathrm{com}_{ij} = (\Diamond_j\Diamond_i p \to \Diamond_i\Diamond_j p) \wedge (\Diamond_i\Diamond_j p \to \Diamond_j\Diamond_i p)$ and $\mathrm{chr}_{ij} = \Diamond_i\Box_j p \to \Box_j\Diamond_i p$. The *commutator* $[L_1, \dots, L_n]$ is the smallest $n$-modal logic containing $L_1, \dots, L_n$ (each with its own box) and all $\mathrm{com}_{ij}$ and $\mathrm{chr}_{ij}$ for $i \neq j$. Always $[L_1, \dots, L_n] \subseteq L_1 \times \cdots \times L_n$, and the commutator of finitely axiomatizable logics is finitely axiomatizable.

**Depth.** For a transitive frame, a point has *cluster-depth* $n$ if the longest path starting from it through points of distinct clusters has $n$ steps, and cluster-depth $\infty$ if there are such paths of every finite length; the cluster-depth of a frame is the supremum over its points, and that of a bimodal frame with transitive relations is the minimum over its two relations.

## Depends on

- [Kripke model](../../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

Product frames validate $\mathrm{com}_{ij}$ and $\mathrm{chr}_{ij}$, which express left and right commutativity and the Church–Rosser property. When $L_1 \times L_2 = [L_1, L_2]$ the pair is called product-matching; this holds for Kripke complete Horn axiomatizable logics (Theorem 21), for example $\mathbf{K4} \times \mathbf{K4} = [\mathbf{K4}, \mathbf{K4}]$. The *global consequence relation* of a logic $L$ holds between $\varphi$ and $\psi$ when $\psi$ is true throughout every model, based on a frame for $L$, in which $\varphi$ is true throughout.

## Sources

- A. Kurucz, "Combining modal logics", in P. Blackburn, J. van Benthem and F. Wolter (eds.), *Handbook of Modal Logic*, Studies in Logic and Practical Reasoning 3, Elsevier, 2007, pp. 869–924, doi:10.1016/S1570-2464(07)80018-8; read in the author's open-access copy at <https://kuag19.github.io/homepage/combi.pdf>: Definitions 10, 11 and 18 (products and commutators), Theorem 21, the definition of cluster-depth before Theorem 34, and Section 3.
