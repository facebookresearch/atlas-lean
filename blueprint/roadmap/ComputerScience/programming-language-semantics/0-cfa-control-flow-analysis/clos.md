# Closures

The closure `mk x body l env` pairs the abstraction `lam x body l` with the
environment `env` in which it was evaluated. An environment is a list of bindings of names to
closures, newest binding first.
