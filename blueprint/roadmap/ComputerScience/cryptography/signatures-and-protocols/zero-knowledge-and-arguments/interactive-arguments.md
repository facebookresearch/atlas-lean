# Interactive arguments

In an interactive proof for a function $f$, a verifier $V$ running in probabilistic polynomial time and a prover $P$ exchange messages $m_1, \dots, m_k$, of total length polynomial in $n$, on a common input $x \in \{0,1\}^n$, alternating between the two parties: each message is computed from $x$ and the earlier messages, and the verifier's messages also from its internal randomness $r$. The prover first claims a value $y$ for $f(x)$, and at the end $V$ outputs $1$ (accept) or $0$ (reject); write $\mathrm{out}(V, x, r, P)$ for this output against a deterministic prover strategy $P$. The pair $(V, P)$ has *completeness error* $\delta_c$ and *soundness error* $\delta_s$ if

- *completeness*: for every $x$, $\Pr_r[\mathrm{out}(V, x, r, P) = 1] \ge 1 - \delta_c$; and
- *soundness*: for every $x$ and every deterministic prover strategy $P'$ that claims a value $y \ne f(x)$, $\Pr_r[\mathrm{out}(V, x, r, P') = 1] \le \delta_s$.

An *argument system* for $f$ is defined in the same way, except that the soundness condition is required only for prover strategies $P'$ that run in polynomial time (*computational soundness*); soundness against all prover strategies is *statistical* soundness.

## Sources

- J. Thaler, *Proofs, Arguments, and Zero-Knowledge*, Foundations and Trends in Privacy and Security 4(2–4), 2022, <https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf>, Section 3.1, Definitions 3.1 and 3.2
