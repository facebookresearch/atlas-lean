# Isolated Read

Exactly one read starts at `p`, and every other read starts more than `W` positions after
`p` and more than `W` positions before it (circularly): a read alone in its apparent island.
