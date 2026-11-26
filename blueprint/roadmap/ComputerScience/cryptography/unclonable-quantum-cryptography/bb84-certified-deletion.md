# Information-theoretic certified deletion from BB84 states

Broadbent–Islam's one-time secret-key scheme for $n$-bit messages uses $m=s+k$ qubits. The key is a basis string $\theta\in\{0,1\}^{m}$ of Hamming weight $k$, check bits $r|_{\bar I}$ on the Hadamard positions $\bar I=\{i:\theta_i=1\}$, a one-time pad $u\in\{0,1\}^{n}$, masks for an error-correction hash and syndrome, and functions $H_{\mathrm{pa}}:\{0,1\}^{s}\to\{0,1\}^{n}$, $H_{\mathrm{ec}}$ drawn from universal$_2$ families. Encryption samples $r|_I$ on the $s$ computational positions $I=\{i:\theta_i=0\}$ and outputs the BB84 state $|r\rangle_\theta$ together with $\mathsf{msg}\oplus H_{\mathrm{pa}}(r|_I)\oplus u$ and the masked hash and syndrome of $r|_I$. Deletion measures every qubit in the Hadamard basis and outputs the outcome $y$; verification accepts when $y$ and $r$ differ on fewer than $k\delta$ positions of $\bar I$, for a tolerated error rate $\delta$. The scheme is certified-deletion secure in the accept-and-distinguish sense, with no computational assumption: for every attack, $|p_0-p_1|\le\eta$, where $p_b$ is the probability that the certificate is accepted *and* the adversary, given the whole key after deletion, outputs $1$ in the game with challenge $b$, and

$$
\eta=O\bigl(2^{(n-s(1-h(\delta+\nu)))/2}+\exp(-sk^{2}\nu^{2}/(m(k+1)))\bigr)
$$

for every $\nu\in(0,\tfrac12-\delta]$, with $h$ the binary entropy; this is negligible when $s$ and $k$ grow fast enough relative to $n$.

## Proof sketch

Purify the encryption so that the computational-basis values are measured after the adversary outputs its certificate. A sampling argument shows that, except with probability $O(\exp(-sk^{2}\nu^{2}/(m(k+1))))$, an accepted Hadamard-basis certificate implies an error rate below $\delta+\nu$ on the unchecked positions as well; an uncertainty relation then gives min-entropy at least about $s(1-h(\delta+\nu))$ of $r|_I$ given the adversary's system, jointly with the acceptance event. The leftover hash lemma turns this into closeness of $H_{\mathrm{pa}}(r|_I)$ to uniform, so on acceptance the pad hides $\mathsf{msg}$, and the bound is on the joint event rather than on a conditioned state.

## Depends on

- [Encryption with certified deletion](certified-deletion.md)

## Proof depends on

- [Leftover hash lemma](../randomness-extraction/leftover-hash-lemma.md)

## Sources

- Anne Broadbent, Rabib Islam, "Quantum Encryption with Certified Deletion", TCC (2020).
