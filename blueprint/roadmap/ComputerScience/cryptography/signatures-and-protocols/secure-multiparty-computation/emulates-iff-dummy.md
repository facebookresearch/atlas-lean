# Dummy sufficiency for one exchange

Testing the two-way forwarding intermediary against
every environment is equivalent to testing all intermediaries. The enlarged environment runs the
real intermediary internally; the new simulator composes that intermediary with the dummy's
simulator. Both are programs of the same uniform polynomial-clock language. This equivalence is
qualitative; the extra gates need not preserve numerical overhead or slack.

## Sources

- fixed-schedule instance of the reduction in R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School (2025), slides 50–53.
