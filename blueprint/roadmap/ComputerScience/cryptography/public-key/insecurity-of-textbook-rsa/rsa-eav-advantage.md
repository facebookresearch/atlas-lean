# Textbook RSA is not eavesdropping-secure

For every distribution of RSA keys, the eavesdropping attack on textbook RSA has advantage
$\tfrac{1}{2}$ in the eavesdropping experiment with messages in $\mathbb{Z}/n$ (Katz and Lindell,
Sections 11.2.1 and 11.5.1). Both of its messages are units, so it also has advantage $\tfrac{1}{2}$
against plain RSA with plaintext space $(\mathbb{Z}/n)^\times$ (stated here without proof).
