# Merge Lo Copy B memmove equation

Public equation for the `CopyB` tail's same-store block move.  The right
remainder uses the `.loCopyBTail` overlap-safe memmove wrapper before the final
temporary A entry is installed.
