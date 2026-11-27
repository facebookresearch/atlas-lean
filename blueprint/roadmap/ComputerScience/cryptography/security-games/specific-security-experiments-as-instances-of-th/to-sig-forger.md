# Lamport one-time forger as a signature forger

Let $R$ be finite and nonempty. A Lamport one-time forger $A = (\mathrm{choose}, \mathrm{forge})$ with coins in $R$ becomes a signature forger: the embedded signature forger draws its coins $r$ uniformly from $R$; on public key $pk$ it makes one signing query, on the message $\mathrm{choose}(pk, r)$, and on the answer $\sigma$ outputs $\mathrm{forge}(pk, \sigma, r)$ with the same coins $r$.
