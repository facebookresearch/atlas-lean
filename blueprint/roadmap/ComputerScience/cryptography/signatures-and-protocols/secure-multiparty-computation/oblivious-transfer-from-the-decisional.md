# Oblivious transfer from the decisional Diffie–Hellman assumption

In 1-out-of-2 oblivious transfer over a cyclic group $\mathbb{G}$ the sender holds messages $x_0, x_1 \in \mathbb{G}$ and the receiver a bit $b$; the receiver should learn $x_b$ and nothing else, and the
sender nothing. Assume a public-key encryption scheme in which a public key can be sampled from the public-key space without learning a
corresponding secret key. The protocol:

1. the receiver generates a key pair $(sk, pk)$ and samples a public key $pk'$ obliviously, and sends $(pk_0, pk_1) = (pk, pk')$ if $b = 0$ and $(pk', pk)$ if $b = 1$;
2. the sender returns $e_0 = \mathrm{Enc}_{pk_0}(x_0)$ and $e_1 = \mathrm{Enc}_{pk_1}(x_1)$;
3. the receiver decrypts $e_b$ with $sk$.

The protocol is secure against semi-honest adversaries. The sender's view consists of two public keys with the same distribution, so it is
simulated by two random public keys. The receiver's view is simulated from $b$ and $x_b$ by encrypting $x_b$ under its key and an arbitrary value under
the obliviously sampled key, which is indistinguishable by the semantic security of the scheme. ElGamal encryption in $\mathbb{G}$, whose messages are group elements, satisfies the
hypotheses under the decisional Diffie–Hellman assumption: a public key is a uniform group element, which can be sampled without its discrete
logarithm, and ElGamal is CPA-secure when DDH is hard.

## Depends on

- [Two-party security against semi-honest adversaries](two-party-security-against-semi-honest.md)

## Proof depends on

- [ElGamal is CPA-secure if DDH is hard](../../public-key/cpa-security-of-elgamal/cpa-advantage-eq-ddh-advantage.md)

## Sources

- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, <https://securecomputation.org/docs/pragmaticmpc.pdf>: Definition 2.5 (oblivious transfer), Section 3.7.1 and Figure 3.6 (public-key based semi-honest OT and its simulators). The ElGamal instantiation is derived on this page.
