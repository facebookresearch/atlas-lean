# Protocol insecurity with finitely many sessions

In the model of Rusinowitch and Turuani, messages are [Dolev–Yao terms](dolev-yao-terms-and-deduction.md) built from atoms and keys by pairing $\langle a, b\rangle$,
public-key encryption $\{a\}^p_K$ and symmetric encryption $\{a\}^s_b$ with arbitrary (composed) keys. A *protocol* is a finite set of steps
$\{(\iota, R_\iota \Rightarrow S_\iota) \mid \iota \in I\}$, where $I = \{(A, i) \mid A \text{ a principal}, i \in W_A\}$, each $W_A$ is partially ordered by $<_{W_A}$, and in step $\iota$
the principal expects a message matching $R_\iota$ and answers with $S_\iota$; variables are global to the specification. The intruder's knowledge evolves by the
rewrite rules that compose and decompose pairs and encryptions (decrypting $\{a\}^p_K$ with $K^{-1}$ and $\{a\}^s_b$ with $b$); $t \in \mathrm{forge}(E)$ if $t$ is obtained
from the set $E$ by finitely many such rules.

Given an initial intruder knowledge $S_0$ and a term $\mathit{Secret}$, an *attack* is a ground substitution $\sigma$ and a bijection $\pi : I \to \{1, \dots, k\}$, $k = |I|$,
compatible with each order $<_{W_A}$, such that $R_i\sigma \in \mathrm{forge}(S_0, S_1\sigma, \dots, S_{i-1}\sigma)$ for every $1 \le i \le k$ and
$\mathit{Secret} \in \mathrm{forge}(S_0, S_1\sigma, \dots, S_k\sigma)$, where $R_i$ and $S_i$ belong to the step $\pi^{-1}(i)$. Running finitely many sessions in parallel is
modelled by taking the union of renamed copies of the protocol steps. The *protocol insecurity problem* asks whether an attack exists.

## Depends on

- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)

## Sources

- M. Rusinowitch and M. Turuani, "Protocol insecurity with a finite number of sessions, composed keys is NP-complete", *Theoretical Computer Science* 299(1–3), 2003; preprint of 12 March 2002 at <http://www-verimag.imag.fr/~ene/m2p/p4.pdf>: Section 1 (protocol specification, executions and Table 1, the intruder rules), Section 2 (Definitions 1–2) and Section 3 (several sessions $m.P$, Lemma 5).
