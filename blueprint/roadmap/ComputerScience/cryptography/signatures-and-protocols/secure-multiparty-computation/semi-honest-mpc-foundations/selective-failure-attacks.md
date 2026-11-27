# Selective failure attacks

Let $M$ be a protocol in which an honest party with secret input $w$ reconstructs an output from the responses of other participants. A *deviation* replaces the prescribed responses of a corrupted participant by arbitrary ones. The *failure game* for a deviation $\mathrm{dev}$ observes only whether the honest party's execution aborts (or outputs a fixed failure value). The deviation is a *selective failure attack* if the failure probability depends on $w$, and *deterministic* if it determines a predicate of $w$ with certainty; $M$ is *selective-failure free* if for every deviation the failure event is a function of the corrupted participants' view in the passive (honest) execution, together with the deviation's own coins; passive privacy makes the law of that view independent of $w$, so the failure probability is then independent of $w$. (A function of the honest party's view would not do: that view contains $w$.) Typical attacks corrupt one response slot so that failure occurs exactly when the secret selects that slot, or exploit a nonlinear "equals 1" test in the reconstruction.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
