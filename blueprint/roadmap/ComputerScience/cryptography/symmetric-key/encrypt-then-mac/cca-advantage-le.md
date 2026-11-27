# Encrypt-then-MAC is CCA-secure

Let the encryption scheme have explicit randomness and decrypt every encryption, that is,
$\mathrm{Dec}_{k_1}(E(k_1, m, r)) = m$ for every key $k_1$, message $m$ and randomness $r$, and let the
MAC be deterministic with canonical verification. For every chosen-ciphertext adversary $A$ against
encrypt-then-MAC that makes at most $q$ oracle queries,

$$\mathrm{Adv}^{\mathrm{cca}}(A) \le \mathrm{Adv}^{\mathrm{cpa}}(B) + \sum_{j < q} \mathrm{Adv}^{\mathrm{mac}}(\mathcal{F}_j),$$

where $B$ is the CPA reduction against the encryption scheme and $\mathcal{F}_j$ is the MAC forger
guessing index $j$, built with two random tapes of $q$ samples (Katz and Lindell, Section 4.5,
encrypt-then-authenticate with a CPA-secure scheme and a MAC with unique tags). Here
$\mathrm{Adv}^{\mathrm{cca}}(A) = |\Pr[\mathrm{PrivK}^{\mathrm{cca}} = 1] - \tfrac{1}{2}|$ is the guessing
advantage of $A$ against encrypt-then-MAC,
$\mathrm{Adv}^{\mathrm{cpa}}(B) = |\Pr[\mathrm{PrivK}^{\mathrm{cpa}} = 1] - \tfrac{1}{2}|$ is the guessing
advantage of $B$ against the encryption scheme, and
$\mathrm{Adv}^{\mathrm{mac}}(\mathcal{F}_j) = \Pr[\mathrm{Mac}\text{-}\mathrm{forge} = 1]$ is the forgery
probability of $\mathcal{F}_j$ against the MAC. The sum is Katz and Lindell's term
$q \cdot \varepsilon_{\mathrm{Mac}}$, with the guessed index made explicit. The reductions are
admissible: $B$ makes at most $q$ encryption queries and each $\mathcal{F}_j$ at most $q + 1$ tagging
queries.
