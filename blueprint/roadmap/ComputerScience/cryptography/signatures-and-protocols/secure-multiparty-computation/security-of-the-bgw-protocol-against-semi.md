# Security of the BGW protocol against semi-honest adversaries

Let $\mathbb{F}$ be a finite field with more than $n$ elements and $f$ an $n$-party functionality given by an arithmetic circuit over $\mathbb{F}$ with addition,
multiplication and multiplication-by-constant gates. Write $[v]$ for a Shamir sharing of $v$ with threshold $t$: a random polynomial $p$ of degree at most $t$
with $p(0) = v$, of which party $P_i$ holds $p(\xi_i)$, for fixed distinct nonzero evaluation points $\xi_1, \dots, \xi_n \in \mathbb{F}$. In the BGW protocol:

- each input owner shares its input wires;
- addition and multiplication by a constant are computed locally on shares;
- for a multiplication gate each party multiplies its shares locally, giving a point $q(\xi_i)$ on a polynomial $q = p_\alpha p_\beta$ of degree at most $2t$; each party
  shares $q(\xi_i)$ with threshold $t$, and the parties compute a threshold-$t$ sharing of $q(0)$ as the fixed linear (Lagrange) combination of these sharings,
  which requires $2t + 1 \le n$;
- for an output wire every party sends its share to the party that receives that output, which reconstructs the value.

Each wire then carries a threshold-$t$ sharing of its value, any $t$ shares reveal nothing about the shared value, and the protocol securely computes $f$
against up to $t$ semi-honest corrupted parties whenever $2t < n$.

## Depends on

- [Multiparty security against semi-honest adversaries](multiparty-security-against-semi-honest.md)

## Sources

- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, <https://securecomputation.org/docs/pragmaticmpc.pdf>: Definition 2.1 (secret sharing), Definition 2.2 (semi-honest security) and Section 3.3 (the BGW protocol and its honest-majority condition).
