# Hybrid encryption

**Hybrid encryption** (Katz and Lindell, Section 11.3): encapsulate a key with the KEM and
encrypt the message under it with the DEM. Decryption fails when decapsulation fails.
