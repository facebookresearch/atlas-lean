# Acceptance of $m$ sequential rounds

For a Sigma protocol, a statement $x$, a prover whose commitment in a round is $a(\ell)$ and whose
answer to a challenge $e$ is $z(\ell, e)$, where $\ell$ is the list of the challenges of the earlier
rounds in order, and a sequence $c_0, \dots, c_{m-1}$ of challenges, the verifier accepts all $m$
rounds: round $i$ checks the transcript $(a(c_0, \dots, c_{i-1}), c_i, z(c_0, \dots, c_{i-1}, c_i))$.
For $m = 0$ the verifier accepts.
