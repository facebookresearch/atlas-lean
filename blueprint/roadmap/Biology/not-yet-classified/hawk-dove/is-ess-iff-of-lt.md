# Hawk–Dove with costly fights

Let `V > 0` and `C > V`. The mixed strategy `(p, 1 - p)`,
which plays Hawk with probability `p`, is an evolutionarily stable state of the Hawk–Dove matrix
game (`Replicator.IsESS` for `payoffMatrix V C`) if and only if `p = V / C`; in particular
neither pure Hawk (`p = 1`) nor pure Dove (`p = 0`) is an ESS.

## Sources

- Maynard Smith (1982), Ch. 2.
