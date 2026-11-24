# Memmove From Traced phase order

Provenance-sensitive source and phase order.  Shared storage uses the
overlap geometry's direction in both physical phases; distinct storage uses
the forward `memcpyCore?` source order in both phases.  In either branch all
key events precede all optional-values events.
