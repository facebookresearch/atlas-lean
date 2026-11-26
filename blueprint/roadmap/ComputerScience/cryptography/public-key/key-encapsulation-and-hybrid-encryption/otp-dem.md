# One-time pad as a data-encapsulation mechanism

For a finite group $G$, the group one-time pad (Katz and Lindell, Section 11.4.1), with a uniform key
$k$, $\mathrm{Enc}_k(m) = km$ and $\mathrm{Dec}_k(c) = k^{-1}c$, is a data-encapsulation mechanism
whose decryption never fails.
