# The ideal semantic-security experiment

For a length function on messages, an ideal adversary $A'$ (which maps a length and a priori
information to a distribution of guesses), a plaintext distribution $X$, an a priori information
function $h$ and a target function $f$, the experiment draws $x \leftarrow X$, then a guess
$t \leftarrow A'(|x|, h(x))$, and outputs whether $t = f(x)$. The ideal adversary sees neither the
public key nor a ciphertext.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Definition 5.2.2 (the second probability; Goldreich gives $A'$ the string $1^{|X_n|}$ and
  remarks that giving it the encryption key would be pointless).
