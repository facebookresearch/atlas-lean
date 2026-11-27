# The standard intruder theory in multiset rewriting

The *standard intruder* is an [MSR theory](multiset-rewriting-with-existential-quantification.md) that models a Dolev–Yao attacker in two phases, with predicates $D(\cdot)$ for messages it
can decompose, $M(\cdot)$ for its memory and $C(\cdot)$ for messages it can compose, over a sort $\mathrm{msg}$ of messages with pairing $\langle \cdot, \cdot\rangle$. For each
network predicate $N_i$, whose argument list $\vec x$ is read by $D$ and $C$ as one message, the pairing of its fields (so a two-field predicate gives $D(\langle x, y\rangle)$), its rules intercept a message, $N_i(\vec x) \to D(\langle \vec x\rangle)$; decompose and remember, $D(\langle x, y\rangle) \to D(x), D(y)$ and $D(z) \to M(z)$; compose from
memory, $M(x) \to C(x), M(x)$ and $C(x), C(y) \to C(\langle x, y\rangle)$; send, $C(\langle \vec x\rangle) \to N_i(\vec x)$; and generate fresh data, $\to \exists x.\ M(x)$. With black-box encryption,
further rules decrypt a ciphertext in $D$ when the matching decryption key is in memory and encrypt in $C$ under any known encryption key.

## Depends on

- [Multiset rewriting with existential quantification](multiset-rewriting-with-existential-quantification.md)
- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 3.3 (the intruder actions and the rules for interception, decomposition, composition and fresh data), Section 3.4 (black-box encryption) Section 3.5 (the general two-phase intruder theory) and Section 4.4 (the intruder theory of the example, Table 7).
