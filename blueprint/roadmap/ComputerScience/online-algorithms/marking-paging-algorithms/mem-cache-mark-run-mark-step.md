# A page is missed at most once per phase

With positive capacity, after a request for `p`
the page stays cached until a request starts a new phase, so every later request for `p` in the
same phase is a hit.
