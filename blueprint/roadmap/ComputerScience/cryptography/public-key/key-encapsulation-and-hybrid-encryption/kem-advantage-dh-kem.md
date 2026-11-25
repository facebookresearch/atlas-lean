# The Diffie–Hellman KEM is CPA-secure if DDH is hard

Let $g$ generate $G$, $|G| = q$, and let $H : G \to K$ be a uniform key-derivation function: $K$ is
finite and nonempty, and $H$ maps the uniform distribution on $G$ to the uniform distribution on $K$
(a property of the fixed function $H$, not a random oracle). For an adversary $B$ with uniform coins,
the KEM advantage of $B$ against the Diffie–Hellman KEM is exactly half the DDH advantage of the
distinguisher that applies $H$ to its third input and then guesses as $B$ does (Katz and Lindell,
Section 11.4.2).
