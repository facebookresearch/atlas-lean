# Merge Hi Copy A memmove equation

Public equation for the `CopyA` tail's same-store block move.  The left
remainder uses the `.hiCopyATail` overlap-safe memmove wrapper before the final
temporary B entry is installed.
