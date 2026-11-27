# Asynchronous atomic broadcast from validated agreement

With $n \ge 3t + 1$ processes, a secure signature scheme and a protocol for multivalued validated asynchronous Byzantine agreement (agreement on a value from an arbitrary domain that satisfies an externally checkable validity predicate), asynchronous Byzantine atomic broadcast (total-order broadcast of payload messages with agreement, validity, total order and fairness) is implemented by Protocol ABC of Cachin, Kursawe, Petzold and Shoup. Each process keeps a FIFO queue of payload messages not yet delivered. In round $r$ it signs the head $w$ of its queue (or, if its queue is empty, a not-yet-delivered head received from another process) and sends $(r, i, w)$ with its signature to all processes; after receiving $n - t$ such signed heads from distinct processes it proposes the vector $W=[w_1,\dots,w_n]$ of these heads together with the vector of signatures. The validity predicate of the $r$-th agreement instance accepts a vector exactly when at least $n - t$ of its entries carry a valid signature by their process on $(r, j, w_j)$. When the instance decides a vector $V=[v_1,\dots,v_n]$, every correct process delivers the payloads in $\bigcup_j v_j$ that it has not yet delivered, in a fixed deterministic order, removes them from its queue and moves to round $r+1$. A proposal thus contains $n - t$ signed queue heads, hence $\Theta(n)$ individual signatures: it is not one constant-size word, so the expected $O(n^2)$-word cost of a validated agreement protocol counting a constant number of signatures per word does not directly bound a round of Protocol ABC.

## Proof sketch

Agreement and total order follow from agreement of each validated agreement instance and the deterministic delivery order. A decided vector is externally valid, so it contains the signed heads of $n - t$ distinct processes, at least $n - 2t \ge t + 1$ of them correct. For fairness, if $t + 1$ correct processes have nonempty queues, at least one of them signed its oldest undelivered payload in every decided vector, so the oldest payloads of correct processes are delivered within a bounded number of rounds; a payload remains in the queue of its correct sender until delivered, and a correct process enters a round only when it knows an undelivered payload.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Validated asynchronous Byzantine agreement with optimal expected quadratic communication](validated-asynchronous-byzantine-agreement-optimal.md)

## Sources

- C. Cachin, K. Kursawe, F. Petzold, V. Shoup, "Secure and Efficient Asynchronous Broadcast Protocols", CRYPTO 2001, Section 5.2 (Protocol ABC, Figure 5, Theorem 12).
- I. Abraham, D. Malkhi, A. Spiegelman, "Asymptotically Optimal Validated Asynchronous Byzantine Agreement", PODC 2019.
