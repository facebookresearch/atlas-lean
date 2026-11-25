# Constant-time programs as leakage noninterference

Consider while programs over arrays with a small-step semantics on configurations $c = \langle s, p \rangle$ of a state $s$ and a program $p$. A *leakage model* $L$
maps configurations to observations and extends to executions by concatenation, $L(c_1 \cdots c_n) = L(c_1) \cdots L(c_n)$; two executions $\alpha$ and $\beta$ are
*indistinguishable* when $L(\alpha) = L(\beta)$. Every leakage model considered exposes the valuations of branch conditions,
$\langle s, \mathbf{if}\ e\ \mathbf{then}\ p_1\ \mathbf{else}\ p_2 \rangle \mapsto s(e)$ and $\langle s, \mathbf{while}\ e\ \mathbf{do}\ p \rangle \mapsto s(e)$, and richer models add further observations, for example the operands of variable-time
operations.

For a set $X$ of program variables, two configurations are *$X$-equivalent* if their states agree on every entry of every array in $X$. Fix a set $X_i$ of
public inputs and a set $X_o$ of publicly observable outputs. A program is *constant-time secure* (for $L$, $X_i$ and $X_o$) when every two complete executions
that are initially $X_i$-equivalent and finally $X_o$-equivalent are indistinguishable, and every two infinite executions that are initially $X_i$-equivalent
have equal leakage, where the leakage of an infinite execution $c_1 c_2 \cdots$ is the infinite sequence $L(c_1) L(c_2) \cdots$ and two such sequences are
equal when they agree at every position. The second clause keeps a program whose nontermination depends on secrets from being accepted vacuously.

Unlike termination-insensitive noninterference, which requires $X_i$-equivalent executions to end $X_o$-equivalent, this policy requires equal leakage of
all executions whose public inputs and outputs agree.

## Depends on

- [Security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)

## Sources

- J. B. Almeida, M. Barbosa, G. Barthe, F. Dupressoir and M. Emmi, "Verifying constant-time implementations", *USENIX Security 2016*, <https://www.usenix.org/system/files/conference/usenixsecurity16/sec16_paper_almeida.pdf>: Section 3 (Figures 5–6, leakage models, Example 1 and the operand-leakage example, $X$-equivalence, Definition 1 and the comparison with noninterference).
