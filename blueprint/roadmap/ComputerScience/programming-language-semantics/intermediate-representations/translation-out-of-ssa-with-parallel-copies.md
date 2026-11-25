# Translation out of SSA with parallel copies

A program in [static single assignment form](dominance-and-static-single-assignment-form.md) can be translated out of SSA form, even after optimizations have made its form non-conventional, as follows.

1. **Split critical edges.** A critical edge goes from a block with several successors to a block with several predecessors. Split each one by inserting a fresh block on it.
2. **Insert parallel copies.** Replace the $\varphi$-functions at the head of each block by copies at the end of the predecessor blocks. Since the $\varphi$-functions at a block head execute simultaneously, the copies inserted at the end of one predecessor form a single *parallel copy* $b_1 \leftarrow a_1 \parallel \dots \parallel b_k \leftarrow a_k$. It assigns all its targets at once from the values of its sources.
3. **Sequentialize.** Replace each parallel copy by a sequence of ordinary copies. While some copy $b \leftarrow a$ with $a \ne b$ remains, emit a copy whose target $b$ is not the source of any remaining copy and delete it. If there is none, the remaining copies form cycles: pick $b \leftarrow a$, emit $a' \leftarrow a$ for a fresh variable $a'$, and replace $b \leftarrow a$ by $b \leftarrow a'$. The number of emitted copies is the number of non-self edges plus the number of cycles of the copy graph. Correctness follows from the invariant that the emitted sequence followed by the remaining parallel copy behaves like the original parallel copy.

Executing the copies of step 2 one by one instead, in an arbitrary order, can change the result when one copy's target is another's source. The *lost-copy* and *swap* problems are examples.

## Depends on

- [Dominance and static single assignment form](dominance-and-static-single-assignment-form.md)

## Sources

- F. Rastello and F. Bouchez Tichadou (eds.), *SSA-based Compiler Design*, Springer, 2022; public draft of 8 June 2018, <https://pfalcon.github.io/ssabook/latest/book-full.pdf>, Section 3.2: critical-edge splitting and parallel copies (Algorithm 3.5), and the sequentialization of parallel copies (Algorithm 3.6) with its termination count and correctness invariant; Section 1.2 on the parallel semantics of $\varphi$-functions.
- P. Briggs, K. D. Cooper, T. J. Harvey and L. T. Simpson, "Practical improvements to the construction and destruction of static single assignment form", *Software: Practice and Experience* 28(8):859–881, 1998.
- B. Boissinot, A. Darte, F. Rastello, B. Dupont de Dinechin and C. Guillon, "Revisiting out-of-SSA translation for correctness, code quality and efficiency", *CGO 2009*.
