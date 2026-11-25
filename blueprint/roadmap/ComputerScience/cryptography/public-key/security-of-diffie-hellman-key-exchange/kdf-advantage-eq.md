# Key derivation preserves eavesdropping security

If $g$ generates $G$, $|G| = q$ and $H$ is a uniform key-derivation function, the key-exchange advantage
of an eavesdropper $E$ against keys derived by $H$ is exactly half the DDH advantage of the
distinguisher built from $E$ and $H$.
