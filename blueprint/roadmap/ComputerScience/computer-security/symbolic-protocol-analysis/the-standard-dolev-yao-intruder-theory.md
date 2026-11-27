# The standard intruder theory in multiset rewriting

The *standard intruder* is an [MSR theory](multiset-rewriting-with-existential-quantification.md) that models a Dolev–Yao attacker in two phases (the two-phase intruder theory of
Table 7 of the source), with predicates $D(\cdot)$ for messages it can decompose, $M(\cdot)$ for its memory, $C(\cdot)$ for messages it can compose and an auxiliary $A(\cdot)$ for
ciphertexts kept for later decryption, over a sort $\mathrm{msg}$ of messages with pairing $\langle \cdot, \cdot\rangle$. It meets the protocol only through the roles' network ports: for
the send predicates $NS_i$ and receive predicates $NR_i$ of the roles, it intercepts from a send port, $NS_i(\vec x) \to D(\langle \vec x\rangle)$, and transmits to a receive port,
$C(\langle \vec x\rangle) \to NR_i(\vec x)$, the argument list $\vec x$ of a network fact being read as one message, the pairing of its fields. Its other rules decompose and remember,
$D(\langle x, y\rangle) \to D(x), D(y)$ and $D(z) \to M(z)$; compose from memory, $M(x) \to C(x), M(x)$ and $C(x), C(y) \to C(\langle x, y\rangle)$; and generate fresh data, $\to \exists x.\ M(x)$.
With black-box encryption, further rules decrypt a ciphertext in $D$ when the matching decryption key is in memory, keep a ciphertext whose key is not yet known as an $A$ fact and
decrypt it once the key is learned, and encrypt in $C$ under any known encryption key. (The encryption-free illustration of Section 3.3 of the source instead uses one family of
network predicates $N_i$, with both interception $N_i(\vec x) \to D$ and transmission $C \to N_i(\vec x)$; that variant is not the intruder used below.)

## Depends on

- [Multiset rewriting with existential quantification](multiset-rewriting-with-existential-quantification.md)
- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 3.3 (the intruder actions, illustrated without encryption), Section 3.4 (black-box encryption), Section 3.5 (two-phase theories, Definition 3.10) and Table 7 (the two-phase intruder theory, with REC: $NS_i(x) \to D(x)$, SND: $C(x) \to NR_i(x)$, the delayed-decryption rules LRNA and DECA, and GEN).
